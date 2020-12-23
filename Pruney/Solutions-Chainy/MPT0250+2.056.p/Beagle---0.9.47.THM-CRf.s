%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:39 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 103 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 110 expanded)
%              Number of equality atoms :   22 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_379,plain,(
    ! [A_103,C_104,B_105] :
      ( r1_tarski(A_103,k2_xboole_0(C_104,B_105))
      | ~ r1_tarski(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_506,plain,(
    ! [A_123,C_124,B_125] :
      ( k3_xboole_0(A_123,k2_xboole_0(C_124,B_125)) = A_123
      | ~ r1_tarski(A_123,B_125) ) ),
    inference(resolution,[status(thm)],[c_379,c_8])).

tff(c_50,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_196,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_229,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_196])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_246,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_2])).

tff(c_512,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_246])).

tff(c_547,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_232,plain,(
    ! [A_10,B_11] : k3_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = A_10 ),
    inference(resolution,[status(thm)],[c_10,c_196])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_752,plain,(
    ! [A_141,B_142] : k5_xboole_0(k5_xboole_0(A_141,B_142),k3_xboole_0(A_141,B_142)) = k2_xboole_0(A_141,B_142) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1198,plain,(
    ! [A_150,B_151] : k5_xboole_0(k5_xboole_0(A_150,B_151),k3_xboole_0(B_151,A_150)) = k2_xboole_0(B_151,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_752])).

tff(c_837,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_752])).

tff(c_1219,plain,(
    ! [B_151,A_150] : k2_xboole_0(B_151,A_150) = k2_xboole_0(A_150,B_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_1198,c_837])).

tff(c_1368,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) = k2_xboole_0('#skF_2',k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_246])).

tff(c_1371,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_1368])).

tff(c_1483,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_10])).

tff(c_1487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_547,c_1483])).

tff(c_1488,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_16,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_301,plain,(
    ! [B_85,C_86,A_87] :
      ( r2_hidden(B_85,C_86)
      | ~ r1_tarski(k2_tarski(A_87,B_85),C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_324,plain,(
    ! [B_91,A_92,B_93] : r2_hidden(B_91,k2_xboole_0(k2_tarski(A_92,B_91),B_93)) ),
    inference(resolution,[status(thm)],[c_10,c_301])).

tff(c_331,plain,(
    ! [A_17,B_93] : r2_hidden(A_17,k2_xboole_0(k1_tarski(A_17),B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_324])).

tff(c_1514,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_331])).

tff(c_1524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1514])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:57:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.55  
% 3.39/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.55  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.39/1.55  
% 3.39/1.55  %Foreground sorts:
% 3.39/1.55  
% 3.39/1.55  
% 3.39/1.55  %Background operators:
% 3.39/1.55  
% 3.39/1.55  
% 3.39/1.55  %Foreground operators:
% 3.39/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.39/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.39/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.39/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.39/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.39/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.39/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.55  
% 3.39/1.56  tff(f_85, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.39/1.56  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.39/1.56  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.39/1.56  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.39/1.56  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.39/1.56  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.39/1.56  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.39/1.56  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.39/1.56  tff(f_80, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.39/1.56  tff(c_48, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.39/1.56  tff(c_379, plain, (![A_103, C_104, B_105]: (r1_tarski(A_103, k2_xboole_0(C_104, B_105)) | ~r1_tarski(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.56  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.56  tff(c_506, plain, (![A_123, C_124, B_125]: (k3_xboole_0(A_123, k2_xboole_0(C_124, B_125))=A_123 | ~r1_tarski(A_123, B_125))), inference(resolution, [status(thm)], [c_379, c_8])).
% 3.39/1.56  tff(c_50, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.39/1.56  tff(c_196, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.56  tff(c_229, plain, (k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_196])).
% 3.39/1.56  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.56  tff(c_246, plain, (k3_xboole_0('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_229, c_2])).
% 3.39/1.56  tff(c_512, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_506, c_246])).
% 3.39/1.56  tff(c_547, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_512])).
% 3.39/1.56  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.39/1.56  tff(c_232, plain, (![A_10, B_11]: (k3_xboole_0(A_10, k2_xboole_0(A_10, B_11))=A_10)), inference(resolution, [status(thm)], [c_10, c_196])).
% 3.39/1.56  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.56  tff(c_752, plain, (![A_141, B_142]: (k5_xboole_0(k5_xboole_0(A_141, B_142), k3_xboole_0(A_141, B_142))=k2_xboole_0(A_141, B_142))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.39/1.56  tff(c_1198, plain, (![A_150, B_151]: (k5_xboole_0(k5_xboole_0(A_150, B_151), k3_xboole_0(B_151, A_150))=k2_xboole_0(B_151, A_150))), inference(superposition, [status(thm), theory('equality')], [c_4, c_752])).
% 3.39/1.56  tff(c_837, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_752])).
% 3.39/1.56  tff(c_1219, plain, (![B_151, A_150]: (k2_xboole_0(B_151, A_150)=k2_xboole_0(A_150, B_151))), inference(superposition, [status(thm), theory('equality')], [c_1198, c_837])).
% 3.39/1.56  tff(c_1368, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))=k2_xboole_0('#skF_2', k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_246])).
% 3.39/1.56  tff(c_1371, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_232, c_1368])).
% 3.39/1.56  tff(c_1483, plain, (r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1371, c_10])).
% 3.39/1.56  tff(c_1487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_547, c_1483])).
% 3.39/1.56  tff(c_1488, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_512])).
% 3.39/1.56  tff(c_16, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.56  tff(c_301, plain, (![B_85, C_86, A_87]: (r2_hidden(B_85, C_86) | ~r1_tarski(k2_tarski(A_87, B_85), C_86))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.56  tff(c_324, plain, (![B_91, A_92, B_93]: (r2_hidden(B_91, k2_xboole_0(k2_tarski(A_92, B_91), B_93)))), inference(resolution, [status(thm)], [c_10, c_301])).
% 3.39/1.56  tff(c_331, plain, (![A_17, B_93]: (r2_hidden(A_17, k2_xboole_0(k1_tarski(A_17), B_93)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_324])).
% 3.39/1.56  tff(c_1514, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1488, c_331])).
% 3.39/1.56  tff(c_1524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1514])).
% 3.39/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.56  
% 3.39/1.56  Inference rules
% 3.39/1.56  ----------------------
% 3.39/1.56  #Ref     : 0
% 3.39/1.56  #Sup     : 388
% 3.39/1.56  #Fact    : 0
% 3.39/1.56  #Define  : 0
% 3.39/1.56  #Split   : 1
% 3.39/1.56  #Chain   : 0
% 3.39/1.56  #Close   : 0
% 3.39/1.56  
% 3.39/1.56  Ordering : KBO
% 3.39/1.56  
% 3.39/1.56  Simplification rules
% 3.39/1.56  ----------------------
% 3.39/1.56  #Subsume      : 26
% 3.39/1.56  #Demod        : 131
% 3.39/1.56  #Tautology    : 130
% 3.39/1.56  #SimpNegUnit  : 2
% 3.39/1.56  #BackRed      : 7
% 3.39/1.56  
% 3.39/1.56  #Partial instantiations: 0
% 3.39/1.56  #Strategies tried      : 1
% 3.39/1.56  
% 3.39/1.56  Timing (in seconds)
% 3.39/1.56  ----------------------
% 3.39/1.57  Preprocessing        : 0.32
% 3.39/1.57  Parsing              : 0.17
% 3.39/1.57  CNF conversion       : 0.02
% 3.39/1.57  Main loop            : 0.47
% 3.39/1.57  Inferencing          : 0.15
% 3.39/1.57  Reduction            : 0.19
% 3.39/1.57  Demodulation         : 0.16
% 3.39/1.57  BG Simplification    : 0.03
% 3.39/1.57  Subsumption          : 0.07
% 3.39/1.57  Abstraction          : 0.03
% 3.39/1.57  MUC search           : 0.00
% 3.39/1.57  Cooper               : 0.00
% 3.39/1.57  Total                : 0.82
% 3.39/1.57  Index Insertion      : 0.00
% 3.39/1.57  Index Deletion       : 0.00
% 3.39/1.57  Index Matching       : 0.00
% 3.39/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
