%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:56 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 370 expanded)
%              Number of leaves         :   38 ( 141 expanded)
%              Depth                    :   22
%              Number of atoms          :   65 ( 393 expanded)
%              Number of equality atoms :   49 ( 308 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_88,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_64,plain,(
    ! [C_35] : r2_hidden(C_35,k1_tarski(C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_190,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_195,plain,(
    ! [A_88] : k3_xboole_0(k1_xboole_0,A_88) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_190])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_200,plain,(
    ! [A_88] : k3_xboole_0(A_88,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_2])).

tff(c_270,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_279,plain,(
    ! [A_88] : k5_xboole_0(A_88,k1_xboole_0) = k4_xboole_0(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_270])).

tff(c_294,plain,(
    ! [A_88] : k4_xboole_0(A_88,k1_xboole_0) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_279])).

tff(c_329,plain,(
    ! [A_96,B_97] : k4_xboole_0(A_96,k4_xboole_0(A_96,B_97)) = k3_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_348,plain,(
    ! [A_88] : k4_xboole_0(A_88,A_88) = k3_xboole_0(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_329])).

tff(c_359,plain,(
    ! [A_88] : k4_xboole_0(A_88,A_88) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_348])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_291,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_270])).

tff(c_391,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_291])).

tff(c_90,plain,(
    k2_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_425,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k4_xboole_0(B_104,A_103)) = k2_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_440,plain,(
    ! [A_88] : k5_xboole_0(k1_xboole_0,A_88) = k2_xboole_0(k1_xboole_0,A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_425])).

tff(c_600,plain,(
    ! [A_118,B_119,C_120] : k5_xboole_0(k5_xboole_0(A_118,B_119),C_120) = k5_xboole_0(A_118,k5_xboole_0(B_119,C_120)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_652,plain,(
    ! [A_9,C_120] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_120)) = k5_xboole_0(k1_xboole_0,C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_600])).

tff(c_913,plain,(
    ! [A_132,C_133] : k5_xboole_0(A_132,k5_xboole_0(A_132,C_133)) = k2_xboole_0(k1_xboole_0,C_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_652])).

tff(c_983,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_913])).

tff(c_1005,plain,(
    ! [A_9] : k2_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_983])).

tff(c_677,plain,(
    ! [A_9,C_120] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_120)) = k2_xboole_0(k1_xboole_0,C_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_652])).

tff(c_1125,plain,(
    ! [A_136,C_137] : k5_xboole_0(A_136,k5_xboole_0(A_136,C_137)) = C_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_677])).

tff(c_1782,plain,(
    ! [A_162,B_163] : k5_xboole_0(A_162,k2_xboole_0(A_162,B_163)) = k4_xboole_0(B_163,A_162) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1125])).

tff(c_1831,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1782])).

tff(c_1840,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_1831])).

tff(c_24,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1192,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1125])).

tff(c_1844,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k5_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1840,c_1192])).

tff(c_1853,plain,(
    k3_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1844])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2410,plain,(
    ! [D_183] :
      ( r2_hidden(D_183,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_183,k1_tarski('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1853,c_6])).

tff(c_62,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2566,plain,(
    ! [D_188] :
      ( D_188 = '#skF_7'
      | ~ r2_hidden(D_188,k1_tarski('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2410,c_62])).

tff(c_2578,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_64,c_2566])).

tff(c_2584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:52:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.70  
% 3.85/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.70  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 3.85/1.70  
% 3.85/1.70  %Foreground sorts:
% 3.85/1.70  
% 3.85/1.70  
% 3.85/1.70  %Background operators:
% 3.85/1.70  
% 3.85/1.70  
% 3.85/1.70  %Foreground operators:
% 3.85/1.70  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.85/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.85/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.85/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.85/1.70  tff('#skF_7', type, '#skF_7': $i).
% 3.85/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.85/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.85/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.85/1.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.85/1.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.85/1.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.85/1.70  tff('#skF_8', type, '#skF_8': $i).
% 3.85/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.85/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.85/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.85/1.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.85/1.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.85/1.70  
% 3.85/1.71  tff(f_95, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 3.85/1.71  tff(f_76, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.85/1.71  tff(f_50, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.85/1.71  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.85/1.71  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.85/1.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.85/1.71  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.85/1.71  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.85/1.71  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.85/1.71  tff(f_54, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.85/1.71  tff(f_52, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.85/1.71  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.85/1.71  tff(c_88, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.85/1.71  tff(c_64, plain, (![C_35]: (r2_hidden(C_35, k1_tarski(C_35)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.85/1.71  tff(c_32, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.85/1.71  tff(c_28, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.85/1.71  tff(c_190, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.85/1.71  tff(c_195, plain, (![A_88]: (k3_xboole_0(k1_xboole_0, A_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_190])).
% 3.85/1.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.71  tff(c_200, plain, (![A_88]: (k3_xboole_0(A_88, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_195, c_2])).
% 3.85/1.71  tff(c_270, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.85/1.71  tff(c_279, plain, (![A_88]: (k5_xboole_0(A_88, k1_xboole_0)=k4_xboole_0(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_200, c_270])).
% 3.85/1.71  tff(c_294, plain, (![A_88]: (k4_xboole_0(A_88, k1_xboole_0)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_279])).
% 3.85/1.71  tff(c_329, plain, (![A_96, B_97]: (k4_xboole_0(A_96, k4_xboole_0(A_96, B_97))=k3_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.85/1.71  tff(c_348, plain, (![A_88]: (k4_xboole_0(A_88, A_88)=k3_xboole_0(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_294, c_329])).
% 3.85/1.71  tff(c_359, plain, (![A_88]: (k4_xboole_0(A_88, A_88)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_200, c_348])).
% 3.85/1.71  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.71  tff(c_291, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_270])).
% 3.85/1.71  tff(c_391, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_359, c_291])).
% 3.85/1.71  tff(c_90, plain, (k2_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.85/1.71  tff(c_36, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.85/1.71  tff(c_425, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k4_xboole_0(B_104, A_103))=k2_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.85/1.71  tff(c_440, plain, (![A_88]: (k5_xboole_0(k1_xboole_0, A_88)=k2_xboole_0(k1_xboole_0, A_88))), inference(superposition, [status(thm), theory('equality')], [c_294, c_425])).
% 3.85/1.71  tff(c_600, plain, (![A_118, B_119, C_120]: (k5_xboole_0(k5_xboole_0(A_118, B_119), C_120)=k5_xboole_0(A_118, k5_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.85/1.71  tff(c_652, plain, (![A_9, C_120]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_120))=k5_xboole_0(k1_xboole_0, C_120))), inference(superposition, [status(thm), theory('equality')], [c_391, c_600])).
% 3.85/1.71  tff(c_913, plain, (![A_132, C_133]: (k5_xboole_0(A_132, k5_xboole_0(A_132, C_133))=k2_xboole_0(k1_xboole_0, C_133))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_652])).
% 3.85/1.71  tff(c_983, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_391, c_913])).
% 3.85/1.71  tff(c_1005, plain, (![A_9]: (k2_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_983])).
% 3.85/1.71  tff(c_677, plain, (![A_9, C_120]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_120))=k2_xboole_0(k1_xboole_0, C_120))), inference(demodulation, [status(thm), theory('equality')], [c_440, c_652])).
% 3.85/1.71  tff(c_1125, plain, (![A_136, C_137]: (k5_xboole_0(A_136, k5_xboole_0(A_136, C_137))=C_137)), inference(demodulation, [status(thm), theory('equality')], [c_1005, c_677])).
% 3.85/1.71  tff(c_1782, plain, (![A_162, B_163]: (k5_xboole_0(A_162, k2_xboole_0(A_162, B_163))=k4_xboole_0(B_163, A_162))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1125])).
% 3.85/1.71  tff(c_1831, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_1782])).
% 3.85/1.71  tff(c_1840, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_391, c_1831])).
% 3.85/1.71  tff(c_24, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.85/1.71  tff(c_1192, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1125])).
% 3.85/1.71  tff(c_1844, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k5_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1840, c_1192])).
% 3.85/1.71  tff(c_1853, plain, (k3_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1844])).
% 3.85/1.71  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.85/1.71  tff(c_2410, plain, (![D_183]: (r2_hidden(D_183, k1_tarski('#skF_7')) | ~r2_hidden(D_183, k1_tarski('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1853, c_6])).
% 3.85/1.71  tff(c_62, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.85/1.71  tff(c_2566, plain, (![D_188]: (D_188='#skF_7' | ~r2_hidden(D_188, k1_tarski('#skF_8')))), inference(resolution, [status(thm)], [c_2410, c_62])).
% 3.85/1.71  tff(c_2578, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_64, c_2566])).
% 3.85/1.71  tff(c_2584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_2578])).
% 3.85/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.71  
% 3.85/1.71  Inference rules
% 3.85/1.71  ----------------------
% 3.85/1.71  #Ref     : 0
% 3.85/1.71  #Sup     : 606
% 3.85/1.71  #Fact    : 0
% 3.85/1.71  #Define  : 0
% 3.85/1.71  #Split   : 0
% 3.85/1.71  #Chain   : 0
% 3.85/1.71  #Close   : 0
% 3.85/1.71  
% 3.85/1.71  Ordering : KBO
% 3.85/1.71  
% 3.85/1.71  Simplification rules
% 3.85/1.71  ----------------------
% 3.85/1.71  #Subsume      : 15
% 3.85/1.71  #Demod        : 463
% 3.85/1.71  #Tautology    : 427
% 3.85/1.71  #SimpNegUnit  : 1
% 3.85/1.71  #BackRed      : 4
% 3.85/1.71  
% 3.85/1.71  #Partial instantiations: 0
% 3.85/1.71  #Strategies tried      : 1
% 3.85/1.71  
% 3.85/1.71  Timing (in seconds)
% 3.85/1.71  ----------------------
% 3.85/1.72  Preprocessing        : 0.36
% 3.85/1.72  Parsing              : 0.19
% 3.85/1.72  CNF conversion       : 0.03
% 3.85/1.72  Main loop            : 0.53
% 3.85/1.72  Inferencing          : 0.19
% 3.85/1.72  Reduction            : 0.21
% 3.85/1.72  Demodulation         : 0.16
% 3.85/1.72  BG Simplification    : 0.03
% 3.85/1.72  Subsumption          : 0.08
% 3.85/1.72  Abstraction          : 0.03
% 3.85/1.72  MUC search           : 0.00
% 3.85/1.72  Cooper               : 0.00
% 3.85/1.72  Total                : 0.93
% 3.85/1.72  Index Insertion      : 0.00
% 3.85/1.72  Index Deletion       : 0.00
% 3.85/1.72  Index Matching       : 0.00
% 3.85/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
