%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:55 EST 2020

% Result     : Theorem 9.74s
% Output     : CNFRefutation 9.74s
% Verified   : 
% Statistics : Number of formulae       :   51 (  65 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 (  71 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_36,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_991,plain,(
    ! [A_78,B_79,C_80] : k3_xboole_0(k3_xboole_0(A_78,B_79),C_80) = k3_xboole_0(A_78,k3_xboole_0(B_79,C_80)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_163,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_188,plain,(
    ! [A_8,B_9] : k3_xboole_0(k3_xboole_0(A_8,B_9),A_8) = k3_xboole_0(A_8,B_9) ),
    inference(resolution,[status(thm)],[c_12,c_163])).

tff(c_1010,plain,(
    ! [C_80,B_79] : k3_xboole_0(C_80,k3_xboole_0(B_79,C_80)) = k3_xboole_0(C_80,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_188])).

tff(c_42,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_191,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_163])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4056,plain,(
    ! [A_149,A_147,B_148] : k3_xboole_0(A_149,k3_xboole_0(A_147,B_148)) = k3_xboole_0(A_147,k3_xboole_0(B_148,A_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_991])).

tff(c_4508,plain,(
    ! [A_149] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',A_149)) = k3_xboole_0(A_149,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_4056])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_190,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_7919,plain,(
    ! [B_172,A_173] : k3_xboole_0(B_172,k3_xboole_0(B_172,A_173)) = k3_xboole_0(A_173,B_172) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_4056])).

tff(c_8156,plain,(
    ! [A_149] : k3_xboole_0(k3_xboole_0('#skF_2',A_149),'#skF_1') = k3_xboole_0('#skF_1',k3_xboole_0(A_149,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4508,c_7919])).

tff(c_22683,plain,(
    ! [A_295] : k3_xboole_0(k3_xboole_0('#skF_2',A_295),'#skF_1') = k3_xboole_0('#skF_1',A_295) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_8156])).

tff(c_22975,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_1') = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_22683])).

tff(c_670,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(k1_tarski(A_64),B_65) = B_65
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_682,plain,(
    ! [A_64,B_65] :
      ( k3_xboole_0(k1_tarski(A_64),B_65) = k1_tarski(A_64)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_14])).

tff(c_23166,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22975,c_682])).

tff(c_23266,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_23166])).

tff(c_23268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_23266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.74/3.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.99  
% 9.74/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/3.99  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.74/3.99  
% 9.74/3.99  %Foreground sorts:
% 9.74/3.99  
% 9.74/3.99  
% 9.74/3.99  %Background operators:
% 9.74/3.99  
% 9.74/3.99  
% 9.74/3.99  %Foreground operators:
% 9.74/3.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.74/3.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.74/3.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.74/3.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.74/3.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.74/3.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.74/3.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.74/3.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.74/3.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.74/3.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.74/3.99  tff('#skF_2', type, '#skF_2': $i).
% 9.74/3.99  tff('#skF_3', type, '#skF_3': $i).
% 9.74/3.99  tff('#skF_1', type, '#skF_1': $i).
% 9.74/3.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.74/3.99  tff('#skF_4', type, '#skF_4': $i).
% 9.74/3.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.74/3.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.74/3.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.74/3.99  
% 9.74/4.00  tff(f_72, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 9.74/4.00  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 9.74/4.00  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.74/4.00  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.74/4.00  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.74/4.00  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.74/4.00  tff(f_63, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 9.74/4.00  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 9.74/4.00  tff(c_36, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.74/4.00  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.74/4.00  tff(c_40, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.74/4.00  tff(c_991, plain, (![A_78, B_79, C_80]: (k3_xboole_0(k3_xboole_0(A_78, B_79), C_80)=k3_xboole_0(A_78, k3_xboole_0(B_79, C_80)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.74/4.00  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.74/4.00  tff(c_163, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.74/4.00  tff(c_188, plain, (![A_8, B_9]: (k3_xboole_0(k3_xboole_0(A_8, B_9), A_8)=k3_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_163])).
% 9.74/4.00  tff(c_1010, plain, (![C_80, B_79]: (k3_xboole_0(C_80, k3_xboole_0(B_79, C_80))=k3_xboole_0(C_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_991, c_188])).
% 9.74/4.00  tff(c_42, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.74/4.00  tff(c_191, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_42, c_163])).
% 9.74/4.00  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.74/4.00  tff(c_4056, plain, (![A_149, A_147, B_148]: (k3_xboole_0(A_149, k3_xboole_0(A_147, B_148))=k3_xboole_0(A_147, k3_xboole_0(B_148, A_149)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_991])).
% 9.74/4.00  tff(c_4508, plain, (![A_149]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', A_149))=k3_xboole_0(A_149, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_4056])).
% 9.74/4.00  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.74/4.00  tff(c_190, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_163])).
% 9.74/4.00  tff(c_7919, plain, (![B_172, A_173]: (k3_xboole_0(B_172, k3_xboole_0(B_172, A_173))=k3_xboole_0(A_173, B_172))), inference(superposition, [status(thm), theory('equality')], [c_190, c_4056])).
% 9.74/4.00  tff(c_8156, plain, (![A_149]: (k3_xboole_0(k3_xboole_0('#skF_2', A_149), '#skF_1')=k3_xboole_0('#skF_1', k3_xboole_0(A_149, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4508, c_7919])).
% 9.74/4.00  tff(c_22683, plain, (![A_295]: (k3_xboole_0(k3_xboole_0('#skF_2', A_295), '#skF_1')=k3_xboole_0('#skF_1', A_295))), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_8156])).
% 9.74/4.00  tff(c_22975, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_22683])).
% 9.74/4.00  tff(c_670, plain, (![A_64, B_65]: (k2_xboole_0(k1_tarski(A_64), B_65)=B_65 | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.74/4.00  tff(c_14, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.74/4.00  tff(c_682, plain, (![A_64, B_65]: (k3_xboole_0(k1_tarski(A_64), B_65)=k1_tarski(A_64) | ~r2_hidden(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_670, c_14])).
% 9.74/4.00  tff(c_23166, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22975, c_682])).
% 9.74/4.00  tff(c_23266, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_23166])).
% 9.74/4.00  tff(c_23268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_23266])).
% 9.74/4.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.74/4.00  
% 9.74/4.00  Inference rules
% 9.74/4.00  ----------------------
% 9.74/4.00  #Ref     : 0
% 9.74/4.00  #Sup     : 5680
% 9.74/4.00  #Fact    : 0
% 9.74/4.00  #Define  : 0
% 9.74/4.00  #Split   : 3
% 9.74/4.00  #Chain   : 0
% 9.74/4.00  #Close   : 0
% 9.74/4.00  
% 9.74/4.00  Ordering : KBO
% 9.74/4.00  
% 9.74/4.00  Simplification rules
% 9.74/4.00  ----------------------
% 9.74/4.00  #Subsume      : 116
% 9.74/4.00  #Demod        : 6681
% 9.74/4.00  #Tautology    : 3637
% 9.74/4.00  #SimpNegUnit  : 4
% 9.74/4.00  #BackRed      : 5
% 9.74/4.00  
% 9.74/4.00  #Partial instantiations: 0
% 9.74/4.00  #Strategies tried      : 1
% 9.74/4.00  
% 9.74/4.00  Timing (in seconds)
% 9.74/4.00  ----------------------
% 9.74/4.00  Preprocessing        : 0.30
% 9.74/4.00  Parsing              : 0.16
% 9.74/4.00  CNF conversion       : 0.02
% 9.74/4.00  Main loop            : 2.94
% 9.74/4.00  Inferencing          : 0.51
% 9.74/4.00  Reduction            : 1.82
% 9.74/4.00  Demodulation         : 1.63
% 9.74/4.00  BG Simplification    : 0.07
% 9.74/4.00  Subsumption          : 0.41
% 9.74/4.00  Abstraction          : 0.09
% 9.74/4.00  MUC search           : 0.00
% 9.74/4.00  Cooper               : 0.00
% 9.74/4.00  Total                : 3.26
% 9.74/4.00  Index Insertion      : 0.00
% 9.74/4.00  Index Deletion       : 0.00
% 9.74/4.00  Index Matching       : 0.00
% 9.74/4.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
