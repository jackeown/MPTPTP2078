%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:50 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 175 expanded)
%              Number of leaves         :   24 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :   52 ( 202 expanded)
%              Number of equality atoms :   23 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_74,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_10])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_8])).

tff(c_60,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_28])).

tff(c_89,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_60])).

tff(c_136,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10])).

tff(c_143,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_136,c_8])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_6])).

tff(c_147,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_58])).

tff(c_435,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(A_54,C_55)
      | ~ r1_tarski(k2_tarski(A_54,B_56),C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_446,plain,(
    ! [C_55] :
      ( r2_hidden('#skF_1',C_55)
      | ~ r1_tarski('#skF_3',C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_435])).

tff(c_457,plain,(
    ! [C_55] : r2_hidden('#skF_1',C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_446])).

tff(c_157,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,(
    ! [A_5] : k2_xboole_0('#skF_3',A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_150,c_157])).

tff(c_26,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),B_21) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_100,plain,(
    ! [A_30,A_20] : k2_xboole_0(A_30,k1_tarski(A_20)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_26])).

tff(c_342,plain,(
    ! [A_44,A_45] : k2_xboole_0(A_44,k1_tarski(A_45)) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_100])).

tff(c_350,plain,(
    ! [A_45] : k1_tarski(A_45) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_342])).

tff(c_12,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_579,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(k2_tarski(A_73,B_74),C_75)
      | ~ r2_hidden(B_74,C_75)
      | ~ r2_hidden(A_73,C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1119,plain,(
    ! [A_96,C_97] :
      ( r1_tarski(k1_tarski(A_96),C_97)
      | ~ r2_hidden(A_96,C_97)
      | ~ r2_hidden(A_96,C_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_579])).

tff(c_149,plain,(
    ! [A_6] :
      ( A_6 = '#skF_3'
      | ~ r1_tarski(A_6,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_143,c_8])).

tff(c_1126,plain,(
    ! [A_96] :
      ( k1_tarski(A_96) = '#skF_3'
      | ~ r2_hidden(A_96,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1119,c_149])).

tff(c_1135,plain,(
    ! [A_98] : ~ r2_hidden(A_98,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_1126])).

tff(c_1143,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_457,c_1135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:24:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.42  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.42  
% 2.72/1.42  %Foreground sorts:
% 2.72/1.42  
% 2.72/1.42  
% 2.72/1.42  %Background operators:
% 2.72/1.42  
% 2.72/1.42  
% 2.72/1.42  %Foreground operators:
% 2.72/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.42  
% 2.72/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.72/1.43  tff(f_60, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.72/1.43  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.72/1.43  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.72/1.43  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.43  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.72/1.43  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.72/1.43  tff(f_56, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.72/1.43  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.72/1.43  tff(c_74, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.43  tff(c_28, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.43  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.43  tff(c_51, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_10])).
% 2.72/1.43  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.43  tff(c_58, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_8])).
% 2.72/1.43  tff(c_60, plain, (k2_xboole_0(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_28])).
% 2.72/1.43  tff(c_89, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_74, c_60])).
% 2.72/1.43  tff(c_136, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_89, c_10])).
% 2.72/1.43  tff(c_143, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_136, c_8])).
% 2.72/1.43  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.43  tff(c_150, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_6])).
% 2.72/1.43  tff(c_147, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_58])).
% 2.72/1.43  tff(c_435, plain, (![A_54, C_55, B_56]: (r2_hidden(A_54, C_55) | ~r1_tarski(k2_tarski(A_54, B_56), C_55))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.43  tff(c_446, plain, (![C_55]: (r2_hidden('#skF_1', C_55) | ~r1_tarski('#skF_3', C_55))), inference(superposition, [status(thm), theory('equality')], [c_147, c_435])).
% 2.72/1.43  tff(c_457, plain, (![C_55]: (r2_hidden('#skF_1', C_55))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_446])).
% 2.72/1.43  tff(c_157, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.43  tff(c_164, plain, (![A_5]: (k2_xboole_0('#skF_3', A_5)=A_5)), inference(resolution, [status(thm)], [c_150, c_157])).
% 2.72/1.43  tff(c_26, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), B_21)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.43  tff(c_100, plain, (![A_30, A_20]: (k2_xboole_0(A_30, k1_tarski(A_20))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_74, c_26])).
% 2.72/1.43  tff(c_342, plain, (![A_44, A_45]: (k2_xboole_0(A_44, k1_tarski(A_45))!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_100])).
% 2.72/1.43  tff(c_350, plain, (![A_45]: (k1_tarski(A_45)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_164, c_342])).
% 2.72/1.43  tff(c_12, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.43  tff(c_579, plain, (![A_73, B_74, C_75]: (r1_tarski(k2_tarski(A_73, B_74), C_75) | ~r2_hidden(B_74, C_75) | ~r2_hidden(A_73, C_75))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.43  tff(c_1119, plain, (![A_96, C_97]: (r1_tarski(k1_tarski(A_96), C_97) | ~r2_hidden(A_96, C_97) | ~r2_hidden(A_96, C_97))), inference(superposition, [status(thm), theory('equality')], [c_12, c_579])).
% 2.72/1.43  tff(c_149, plain, (![A_6]: (A_6='#skF_3' | ~r1_tarski(A_6, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_143, c_8])).
% 2.72/1.43  tff(c_1126, plain, (![A_96]: (k1_tarski(A_96)='#skF_3' | ~r2_hidden(A_96, '#skF_3'))), inference(resolution, [status(thm)], [c_1119, c_149])).
% 2.72/1.43  tff(c_1135, plain, (![A_98]: (~r2_hidden(A_98, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_350, c_1126])).
% 2.72/1.43  tff(c_1143, plain, $false, inference(resolution, [status(thm)], [c_457, c_1135])).
% 2.72/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  Inference rules
% 2.72/1.43  ----------------------
% 2.72/1.43  #Ref     : 0
% 2.72/1.43  #Sup     : 260
% 2.72/1.43  #Fact    : 0
% 2.72/1.43  #Define  : 0
% 2.72/1.43  #Split   : 0
% 2.72/1.43  #Chain   : 0
% 2.72/1.43  #Close   : 0
% 2.72/1.43  
% 2.72/1.43  Ordering : KBO
% 2.72/1.43  
% 2.72/1.43  Simplification rules
% 2.72/1.43  ----------------------
% 2.72/1.43  #Subsume      : 17
% 2.72/1.43  #Demod        : 237
% 2.72/1.43  #Tautology    : 200
% 2.72/1.43  #SimpNegUnit  : 1
% 2.72/1.43  #BackRed      : 9
% 2.72/1.43  
% 2.72/1.43  #Partial instantiations: 0
% 2.72/1.43  #Strategies tried      : 1
% 2.72/1.43  
% 2.72/1.43  Timing (in seconds)
% 2.72/1.43  ----------------------
% 2.72/1.43  Preprocessing        : 0.30
% 2.72/1.43  Parsing              : 0.16
% 2.72/1.43  CNF conversion       : 0.02
% 2.72/1.43  Main loop            : 0.38
% 2.72/1.43  Inferencing          : 0.14
% 2.72/1.43  Reduction            : 0.15
% 2.72/1.43  Demodulation         : 0.12
% 2.72/1.43  BG Simplification    : 0.02
% 2.72/1.43  Subsumption          : 0.05
% 2.72/1.43  Abstraction          : 0.02
% 2.72/1.43  MUC search           : 0.00
% 2.72/1.43  Cooper               : 0.00
% 2.72/1.43  Total                : 0.70
% 2.72/1.44  Index Insertion      : 0.00
% 2.72/1.44  Index Deletion       : 0.00
% 2.72/1.44  Index Matching       : 0.00
% 2.72/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
