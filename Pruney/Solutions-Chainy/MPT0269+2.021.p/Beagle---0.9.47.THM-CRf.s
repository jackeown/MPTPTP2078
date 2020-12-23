%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:46 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 116 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   47 ( 107 expanded)
%              Number of equality atoms :   41 ( 101 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85,plain,(
    ! [B_53,A_54] : k5_xboole_0(B_53,A_54) = k5_xboole_0(A_54,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_54] : k5_xboole_0(k1_xboole_0,A_54) = A_54 ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_6])).

tff(c_42,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k2_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_337,plain,(
    ! [A_73,B_74,C_75] : k5_xboole_0(k5_xboole_0(A_73,B_74),C_75) = k5_xboole_0(A_73,k5_xboole_0(B_74,C_75)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4560,plain,(
    ! [A_151,B_152] : k5_xboole_0(A_151,k5_xboole_0(B_152,k2_xboole_0(A_151,B_152))) = k3_xboole_0(A_151,B_152) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_337])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_414,plain,(
    ! [A_11,C_75] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_75)) = k5_xboole_0(k1_xboole_0,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_337])).

tff(c_427,plain,(
    ! [A_11,C_75] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_75)) = C_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_414])).

tff(c_4610,plain,(
    ! [B_152,A_151] : k5_xboole_0(B_152,k2_xboole_0(A_151,B_152)) = k5_xboole_0(A_151,k3_xboole_0(A_151,B_152)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4560,c_427])).

tff(c_4707,plain,(
    ! [B_153,A_154] : k5_xboole_0(B_153,k2_xboole_0(A_154,B_153)) = k4_xboole_0(A_154,B_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4610])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_428,plain,(
    ! [A_76,C_77] : k5_xboole_0(A_76,k5_xboole_0(A_76,C_77)) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_414])).

tff(c_477,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_428])).

tff(c_4936,plain,(
    ! [A_157,B_158] : k5_xboole_0(k2_xboole_0(A_157,B_158),k4_xboole_0(A_157,B_158)) = B_158 ),
    inference(superposition,[status(thm),theory(equality)],[c_4707,c_477])).

tff(c_4996,plain,(
    k5_xboole_0(k2_xboole_0('#skF_1',k1_tarski('#skF_2')),k1_xboole_0) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4936])).

tff(c_1465,plain,(
    ! [A_122,A_120,B_121] : k5_xboole_0(A_122,k5_xboole_0(A_120,B_121)) = k5_xboole_0(A_120,k5_xboole_0(B_121,A_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_337])).

tff(c_1863,plain,(
    ! [A_123,A_124] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_123,A_124)) = k5_xboole_0(A_124,A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_1465])).

tff(c_2107,plain,(
    ! [A_127,A_128] : k5_xboole_0(k5_xboole_0(A_127,A_128),k5_xboole_0(A_128,A_127)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1863,c_477])).

tff(c_2142,plain,(
    ! [A_127,A_128] : k5_xboole_0(k5_xboole_0(A_127,A_128),k1_xboole_0) = k5_xboole_0(A_128,A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_2107,c_427])).

tff(c_5014,plain,(
    k5_xboole_0(k1_xboole_0,k2_xboole_0('#skF_1',k1_tarski('#skF_2'))) = k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4996,c_2142])).

tff(c_5071,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_6,c_5014])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5100,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5071,c_8])).

tff(c_30,plain,(
    ! [B_43,A_42] :
      ( k1_tarski(B_43) = A_42
      | k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_tarski(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5111,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5100,c_30])).

tff(c_5115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_5111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:46:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/2.00  
% 5.07/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/2.00  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 5.07/2.00  
% 5.07/2.00  %Foreground sorts:
% 5.07/2.00  
% 5.07/2.00  
% 5.07/2.00  %Background operators:
% 5.07/2.00  
% 5.07/2.00  
% 5.07/2.00  %Foreground operators:
% 5.07/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.07/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.07/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.07/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.07/2.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.07/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.07/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.07/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.07/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.07/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.07/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.07/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.07/2.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.00  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.07/2.00  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.07/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.07/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.07/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.07/2.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.07/2.00  
% 5.07/2.01  tff(f_71, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 5.07/2.01  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.07/2.01  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.07/2.01  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.07/2.01  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 5.07/2.01  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.07/2.01  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.07/2.01  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.07/2.01  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.07/2.01  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.07/2.01  tff(c_38, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.07/2.01  tff(c_85, plain, (![B_53, A_54]: (k5_xboole_0(B_53, A_54)=k5_xboole_0(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.07/2.01  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.07/2.01  tff(c_101, plain, (![A_54]: (k5_xboole_0(k1_xboole_0, A_54)=A_54)), inference(superposition, [status(thm), theory('equality')], [c_85, c_6])).
% 5.07/2.01  tff(c_42, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.07/2.01  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.07/2.01  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k2_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.07/2.01  tff(c_337, plain, (![A_73, B_74, C_75]: (k5_xboole_0(k5_xboole_0(A_73, B_74), C_75)=k5_xboole_0(A_73, k5_xboole_0(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.07/2.01  tff(c_4560, plain, (![A_151, B_152]: (k5_xboole_0(A_151, k5_xboole_0(B_152, k2_xboole_0(A_151, B_152)))=k3_xboole_0(A_151, B_152))), inference(superposition, [status(thm), theory('equality')], [c_14, c_337])).
% 5.07/2.01  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.07/2.01  tff(c_414, plain, (![A_11, C_75]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_75))=k5_xboole_0(k1_xboole_0, C_75))), inference(superposition, [status(thm), theory('equality')], [c_12, c_337])).
% 5.07/2.01  tff(c_427, plain, (![A_11, C_75]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_75))=C_75)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_414])).
% 5.07/2.01  tff(c_4610, plain, (![B_152, A_151]: (k5_xboole_0(B_152, k2_xboole_0(A_151, B_152))=k5_xboole_0(A_151, k3_xboole_0(A_151, B_152)))), inference(superposition, [status(thm), theory('equality')], [c_4560, c_427])).
% 5.07/2.01  tff(c_4707, plain, (![B_153, A_154]: (k5_xboole_0(B_153, k2_xboole_0(A_154, B_153))=k4_xboole_0(A_154, B_153))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4610])).
% 5.07/2.01  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.07/2.01  tff(c_428, plain, (![A_76, C_77]: (k5_xboole_0(A_76, k5_xboole_0(A_76, C_77))=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_414])).
% 5.07/2.01  tff(c_477, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_428])).
% 5.07/2.01  tff(c_4936, plain, (![A_157, B_158]: (k5_xboole_0(k2_xboole_0(A_157, B_158), k4_xboole_0(A_157, B_158))=B_158)), inference(superposition, [status(thm), theory('equality')], [c_4707, c_477])).
% 5.07/2.01  tff(c_4996, plain, (k5_xboole_0(k2_xboole_0('#skF_1', k1_tarski('#skF_2')), k1_xboole_0)=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_42, c_4936])).
% 5.07/2.01  tff(c_1465, plain, (![A_122, A_120, B_121]: (k5_xboole_0(A_122, k5_xboole_0(A_120, B_121))=k5_xboole_0(A_120, k5_xboole_0(B_121, A_122)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_337])).
% 5.07/2.01  tff(c_1863, plain, (![A_123, A_124]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_123, A_124))=k5_xboole_0(A_124, A_123))), inference(superposition, [status(thm), theory('equality')], [c_101, c_1465])).
% 5.07/2.01  tff(c_2107, plain, (![A_127, A_128]: (k5_xboole_0(k5_xboole_0(A_127, A_128), k5_xboole_0(A_128, A_127))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1863, c_477])).
% 5.07/2.01  tff(c_2142, plain, (![A_127, A_128]: (k5_xboole_0(k5_xboole_0(A_127, A_128), k1_xboole_0)=k5_xboole_0(A_128, A_127))), inference(superposition, [status(thm), theory('equality')], [c_2107, c_427])).
% 5.07/2.01  tff(c_5014, plain, (k5_xboole_0(k1_xboole_0, k2_xboole_0('#skF_1', k1_tarski('#skF_2')))=k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4996, c_2142])).
% 5.07/2.01  tff(c_5071, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_6, c_5014])).
% 5.07/2.01  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.07/2.01  tff(c_5100, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5071, c_8])).
% 5.07/2.01  tff(c_30, plain, (![B_43, A_42]: (k1_tarski(B_43)=A_42 | k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_tarski(B_43)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.07/2.01  tff(c_5111, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_5100, c_30])).
% 5.07/2.01  tff(c_5115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_5111])).
% 5.07/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/2.01  
% 5.07/2.01  Inference rules
% 5.07/2.01  ----------------------
% 5.07/2.01  #Ref     : 0
% 5.07/2.01  #Sup     : 1297
% 5.07/2.01  #Fact    : 0
% 5.07/2.01  #Define  : 0
% 5.07/2.01  #Split   : 0
% 5.07/2.01  #Chain   : 0
% 5.07/2.01  #Close   : 0
% 5.07/2.01  
% 5.07/2.01  Ordering : KBO
% 5.07/2.01  
% 5.07/2.01  Simplification rules
% 5.07/2.01  ----------------------
% 5.07/2.01  #Subsume      : 35
% 5.07/2.01  #Demod        : 1083
% 5.07/2.01  #Tautology    : 690
% 5.07/2.01  #SimpNegUnit  : 1
% 5.07/2.01  #BackRed      : 2
% 5.07/2.01  
% 5.07/2.01  #Partial instantiations: 0
% 5.07/2.01  #Strategies tried      : 1
% 5.07/2.01  
% 5.07/2.01  Timing (in seconds)
% 5.07/2.01  ----------------------
% 5.07/2.02  Preprocessing        : 0.32
% 5.07/2.02  Parsing              : 0.17
% 5.07/2.02  CNF conversion       : 0.02
% 5.07/2.02  Main loop            : 0.92
% 5.07/2.02  Inferencing          : 0.26
% 5.07/2.02  Reduction            : 0.47
% 5.07/2.02  Demodulation         : 0.42
% 5.07/2.02  BG Simplification    : 0.04
% 5.07/2.02  Subsumption          : 0.11
% 5.07/2.02  Abstraction          : 0.05
% 5.07/2.02  MUC search           : 0.00
% 5.07/2.02  Cooper               : 0.00
% 5.07/2.02  Total                : 1.27
% 5.07/2.02  Index Insertion      : 0.00
% 5.07/2.02  Index Deletion       : 0.00
% 5.07/2.02  Index Matching       : 0.00
% 5.07/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
