%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:45 EST 2020

% Result     : Theorem 12.87s
% Output     : CNFRefutation 13.01s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 378 expanded)
%              Number of leaves         :   28 ( 142 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 473 expanded)
%              Number of equality atoms :   75 ( 358 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_34,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,(
    ! [A_38] : k2_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_12])).

tff(c_251,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k2_xboole_0(A_43,B_44)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_261,plain,(
    ! [A_38] : k4_xboole_0(k1_xboole_0,A_38) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_251])).

tff(c_38,plain,(
    r1_xboole_0('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1054,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ r1_xboole_0(A_69,B_70)
      | ~ r2_hidden(C_71,k3_xboole_0(A_69,B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1495,plain,(
    ! [A_84,B_85] :
      ( ~ r1_xboole_0(A_84,B_85)
      | k3_xboole_0(A_84,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_1054])).

tff(c_1503,plain,(
    k3_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_1495])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1565,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_4])).

tff(c_1639,plain,(
    ! [A_86,B_87,C_88] : k4_xboole_0(k3_xboole_0(A_86,B_87),C_88) = k3_xboole_0(A_86,k4_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1697,plain,(
    ! [C_88] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_5',C_88)) = k4_xboole_0(k1_xboole_0,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_1565,c_1639])).

tff(c_1765,plain,(
    ! [C_88] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_5',C_88)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_1697])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_41,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_258,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_251])).

tff(c_1993,plain,(
    ! [A_92,B_93,C_94] : k4_xboole_0(k4_xboole_0(A_92,B_93),C_94) = k4_xboole_0(A_92,k2_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(A_29,B_30),k4_xboole_0(A_29,B_30)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_21255,plain,(
    ! [A_292,B_293,C_294] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_292,B_293),C_294),k4_xboole_0(A_292,k2_xboole_0(B_293,C_294))) = k4_xboole_0(A_292,B_293) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_30])).

tff(c_21559,plain,(
    k2_xboole_0(k3_xboole_0(k4_xboole_0('#skF_5','#skF_4'),'#skF_3'),k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_21255])).

tff(c_21667,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_12,c_4,c_21559])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | k4_xboole_0(B_15,A_14) != k4_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_21777,plain,
    ( '#skF_5' = '#skF_4'
    | k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_21667,c_16])).

tff(c_21822,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_21777])).

tff(c_36,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1502,plain,(
    k3_xboole_0('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1495])).

tff(c_1522,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_6','#skF_4')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1502,c_30])).

tff(c_1795,plain,(
    k4_xboole_0('#skF_6','#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_84])).

tff(c_382,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(B_50,A_49)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_410,plain,(
    k4_xboole_0('#skF_6',k2_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_382])).

tff(c_18,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18467,plain,(
    ! [C_280,A_281,B_282] : k2_xboole_0(C_280,k4_xboole_0(A_281,k2_xboole_0(B_282,C_280))) = k2_xboole_0(C_280,k4_xboole_0(A_281,B_282)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_18])).

tff(c_18678,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_6','#skF_4')) = k2_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_18467])).

tff(c_18771,plain,(
    k2_xboole_0('#skF_3','#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1795,c_12,c_18678])).

tff(c_1631,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_5')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1565,c_30])).

tff(c_2423,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1631,c_84])).

tff(c_264,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_251])).

tff(c_20873,plain,(
    ! [A_291] : k2_xboole_0('#skF_6',k4_xboole_0(A_291,k2_xboole_0('#skF_4','#skF_3'))) = k2_xboole_0('#skF_6',k4_xboole_0(A_291,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_18467])).

tff(c_20996,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_3','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_20873])).

tff(c_21041,plain,(
    '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18771,c_2,c_2423,c_12,c_20996])).

tff(c_1706,plain,(
    ! [C_88] : k3_xboole_0('#skF_6',k4_xboole_0('#skF_4',C_88)) = k4_xboole_0(k1_xboole_0,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_1502,c_1639])).

tff(c_1768,plain,(
    ! [C_88] : k3_xboole_0('#skF_6',k4_xboole_0('#skF_4',C_88)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_1706])).

tff(c_21089,plain,(
    ! [C_88] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_88)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21041,c_1768])).

tff(c_24,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_21011,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_4','#skF_5')) = k2_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_20873])).

tff(c_21045,plain,(
    k2_xboole_0('#skF_6',k4_xboole_0('#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_21011])).

tff(c_26544,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21041,c_21041,c_21045])).

tff(c_26618,plain,(
    k4_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26544,c_264])).

tff(c_398,plain,(
    ! [A_29,B_30] : k4_xboole_0(k4_xboole_0(A_29,B_30),A_29) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_382])).

tff(c_1322,plain,(
    ! [A_80,B_81] : k2_xboole_0(A_80,k4_xboole_0(B_81,A_80)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1356,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k2_xboole_0(A_29,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_1322])).

tff(c_1393,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1356])).

tff(c_26,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1350,plain,(
    ! [A_24,B_25] : k2_xboole_0(k4_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(k4_xboole_0(A_24,B_25),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1322])).

tff(c_1391,plain,(
    ! [A_24,B_25] : k2_xboole_0(k4_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,k4_xboole_0(A_24,B_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1350])).

tff(c_12590,plain,(
    ! [A_24,B_25] : k2_xboole_0(k4_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1393,c_1391])).

tff(c_31039,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(k4_xboole_0('#skF_4','#skF_5'),'#skF_3')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_26618,c_12590])).

tff(c_31139,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_21089,c_84,c_4,c_31039])).

tff(c_31141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21822,c_31139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n025.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:00:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.87/5.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.87/5.04  
% 12.87/5.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.87/5.04  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 12.87/5.04  
% 12.87/5.04  %Foreground sorts:
% 12.87/5.04  
% 12.87/5.04  
% 12.87/5.04  %Background operators:
% 12.87/5.04  
% 12.87/5.04  
% 12.87/5.04  %Foreground operators:
% 12.87/5.04  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.87/5.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.87/5.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.87/5.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.87/5.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.87/5.04  tff('#skF_5', type, '#skF_5': $i).
% 12.87/5.04  tff('#skF_6', type, '#skF_6': $i).
% 12.87/5.04  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.87/5.04  tff('#skF_3', type, '#skF_3': $i).
% 12.87/5.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.87/5.04  tff('#skF_4', type, '#skF_4': $i).
% 12.87/5.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.87/5.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.87/5.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.87/5.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.87/5.04  
% 13.01/5.06  tff(f_84, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 13.01/5.06  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.01/5.06  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.01/5.06  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 13.01/5.06  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 13.01/5.06  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 13.01/5.06  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.01/5.06  tff(f_71, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 13.01/5.06  tff(f_65, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 13.01/5.06  tff(f_73, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 13.01/5.06  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 13.01/5.06  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.01/5.06  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.01/5.06  tff(c_34, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.01/5.06  tff(c_68, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.01/5.06  tff(c_12, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.01/5.06  tff(c_84, plain, (![A_38]: (k2_xboole_0(k1_xboole_0, A_38)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_68, c_12])).
% 13.01/5.06  tff(c_251, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k2_xboole_0(A_43, B_44))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.01/5.06  tff(c_261, plain, (![A_38]: (k4_xboole_0(k1_xboole_0, A_38)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_84, c_251])).
% 13.01/5.06  tff(c_38, plain, (r1_xboole_0('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.01/5.06  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.01/5.06  tff(c_1054, plain, (![A_69, B_70, C_71]: (~r1_xboole_0(A_69, B_70) | ~r2_hidden(C_71, k3_xboole_0(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.01/5.06  tff(c_1495, plain, (![A_84, B_85]: (~r1_xboole_0(A_84, B_85) | k3_xboole_0(A_84, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_1054])).
% 13.01/5.06  tff(c_1503, plain, (k3_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_1495])).
% 13.01/5.06  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.01/5.06  tff(c_1565, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1503, c_4])).
% 13.01/5.06  tff(c_1639, plain, (![A_86, B_87, C_88]: (k4_xboole_0(k3_xboole_0(A_86, B_87), C_88)=k3_xboole_0(A_86, k4_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.01/5.06  tff(c_1697, plain, (![C_88]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_5', C_88))=k4_xboole_0(k1_xboole_0, C_88))), inference(superposition, [status(thm), theory('equality')], [c_1565, c_1639])).
% 13.01/5.06  tff(c_1765, plain, (![C_88]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_5', C_88))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_261, c_1697])).
% 13.01/5.06  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.01/5.06  tff(c_40, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.01/5.06  tff(c_41, plain, (k2_xboole_0('#skF_5', '#skF_6')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40])).
% 13.01/5.06  tff(c_258, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41, c_251])).
% 13.01/5.06  tff(c_1993, plain, (![A_92, B_93, C_94]: (k4_xboole_0(k4_xboole_0(A_92, B_93), C_94)=k4_xboole_0(A_92, k2_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.01/5.06  tff(c_30, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(A_29, B_30), k4_xboole_0(A_29, B_30))=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.01/5.06  tff(c_21255, plain, (![A_292, B_293, C_294]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_292, B_293), C_294), k4_xboole_0(A_292, k2_xboole_0(B_293, C_294)))=k4_xboole_0(A_292, B_293))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_30])).
% 13.01/5.06  tff(c_21559, plain, (k2_xboole_0(k3_xboole_0(k4_xboole_0('#skF_5', '#skF_4'), '#skF_3'), k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_258, c_21255])).
% 13.01/5.06  tff(c_21667, plain, (k4_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_12, c_4, c_21559])).
% 13.01/5.06  tff(c_16, plain, (![B_15, A_14]: (B_15=A_14 | k4_xboole_0(B_15, A_14)!=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.01/5.06  tff(c_21777, plain, ('#skF_5'='#skF_4' | k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_21667, c_16])).
% 13.01/5.06  tff(c_21822, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_21777])).
% 13.01/5.06  tff(c_36, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 13.01/5.06  tff(c_1502, plain, (k3_xboole_0('#skF_6', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_1495])).
% 13.01/5.06  tff(c_1522, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_6', '#skF_4'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1502, c_30])).
% 13.01/5.06  tff(c_1795, plain, (k4_xboole_0('#skF_6', '#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1522, c_84])).
% 13.01/5.06  tff(c_382, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(B_50, A_49))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_251])).
% 13.01/5.06  tff(c_410, plain, (k4_xboole_0('#skF_6', k2_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_41, c_382])).
% 13.01/5.06  tff(c_18, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.01/5.06  tff(c_18467, plain, (![C_280, A_281, B_282]: (k2_xboole_0(C_280, k4_xboole_0(A_281, k2_xboole_0(B_282, C_280)))=k2_xboole_0(C_280, k4_xboole_0(A_281, B_282)))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_18])).
% 13.01/5.06  tff(c_18678, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_6', '#skF_4'))=k2_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_410, c_18467])).
% 13.01/5.06  tff(c_18771, plain, (k2_xboole_0('#skF_3', '#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1795, c_12, c_18678])).
% 13.01/5.06  tff(c_1631, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_5'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1565, c_30])).
% 13.01/5.06  tff(c_2423, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1631, c_84])).
% 13.01/5.06  tff(c_264, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_251])).
% 13.01/5.06  tff(c_20873, plain, (![A_291]: (k2_xboole_0('#skF_6', k4_xboole_0(A_291, k2_xboole_0('#skF_4', '#skF_3')))=k2_xboole_0('#skF_6', k4_xboole_0(A_291, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_41, c_18467])).
% 13.01/5.06  tff(c_20996, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_3', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_264, c_20873])).
% 13.01/5.06  tff(c_21041, plain, ('#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18771, c_2, c_2423, c_12, c_20996])).
% 13.01/5.06  tff(c_1706, plain, (![C_88]: (k3_xboole_0('#skF_6', k4_xboole_0('#skF_4', C_88))=k4_xboole_0(k1_xboole_0, C_88))), inference(superposition, [status(thm), theory('equality')], [c_1502, c_1639])).
% 13.01/5.06  tff(c_1768, plain, (![C_88]: (k3_xboole_0('#skF_6', k4_xboole_0('#skF_4', C_88))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_261, c_1706])).
% 13.01/5.06  tff(c_21089, plain, (![C_88]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_88))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_21041, c_1768])).
% 13.01/5.06  tff(c_24, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.01/5.06  tff(c_21011, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_4', '#skF_5'))=k2_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_20873])).
% 13.01/5.06  tff(c_21045, plain, (k2_xboole_0('#skF_6', k4_xboole_0('#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_21011])).
% 13.01/5.06  tff(c_26544, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21041, c_21041, c_21045])).
% 13.01/5.06  tff(c_26618, plain, (k4_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_26544, c_264])).
% 13.01/5.06  tff(c_398, plain, (![A_29, B_30]: (k4_xboole_0(k4_xboole_0(A_29, B_30), A_29)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_382])).
% 13.01/5.06  tff(c_1322, plain, (![A_80, B_81]: (k2_xboole_0(A_80, k4_xboole_0(B_81, A_80))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.01/5.06  tff(c_1356, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k2_xboole_0(A_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_398, c_1322])).
% 13.01/5.06  tff(c_1393, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k4_xboole_0(A_29, B_30))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1356])).
% 13.01/5.06  tff(c_26, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.01/5.06  tff(c_1350, plain, (![A_24, B_25]: (k2_xboole_0(k4_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(k4_xboole_0(A_24, B_25), A_24))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1322])).
% 13.01/5.06  tff(c_1391, plain, (![A_24, B_25]: (k2_xboole_0(k4_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(A_24, k4_xboole_0(A_24, B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1350])).
% 13.01/5.06  tff(c_12590, plain, (![A_24, B_25]: (k2_xboole_0(k4_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_1393, c_1391])).
% 13.01/5.06  tff(c_31039, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0(k4_xboole_0('#skF_4', '#skF_5'), '#skF_3'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_26618, c_12590])).
% 13.01/5.06  tff(c_31139, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_21089, c_84, c_4, c_31039])).
% 13.01/5.06  tff(c_31141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21822, c_31139])).
% 13.01/5.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.01/5.06  
% 13.01/5.06  Inference rules
% 13.01/5.06  ----------------------
% 13.01/5.06  #Ref     : 1
% 13.01/5.06  #Sup     : 7878
% 13.01/5.06  #Fact    : 0
% 13.01/5.06  #Define  : 0
% 13.01/5.06  #Split   : 5
% 13.01/5.06  #Chain   : 0
% 13.01/5.06  #Close   : 0
% 13.01/5.06  
% 13.01/5.06  Ordering : KBO
% 13.01/5.06  
% 13.01/5.06  Simplification rules
% 13.01/5.06  ----------------------
% 13.01/5.06  #Subsume      : 171
% 13.01/5.06  #Demod        : 9149
% 13.01/5.06  #Tautology    : 5469
% 13.01/5.06  #SimpNegUnit  : 99
% 13.01/5.06  #BackRed      : 58
% 13.01/5.06  
% 13.01/5.06  #Partial instantiations: 0
% 13.01/5.06  #Strategies tried      : 1
% 13.01/5.06  
% 13.01/5.06  Timing (in seconds)
% 13.01/5.06  ----------------------
% 13.01/5.06  Preprocessing        : 0.31
% 13.01/5.06  Parsing              : 0.16
% 13.01/5.06  CNF conversion       : 0.02
% 13.01/5.06  Main loop            : 3.99
% 13.01/5.06  Inferencing          : 0.74
% 13.01/5.06  Reduction            : 2.34
% 13.01/5.06  Demodulation         : 2.08
% 13.01/5.06  BG Simplification    : 0.08
% 13.01/5.06  Subsumption          : 0.63
% 13.01/5.06  Abstraction          : 0.13
% 13.01/5.06  MUC search           : 0.00
% 13.01/5.06  Cooper               : 0.00
% 13.01/5.06  Total                : 4.34
% 13.01/5.06  Index Insertion      : 0.00
% 13.01/5.06  Index Deletion       : 0.00
% 13.01/5.06  Index Matching       : 0.00
% 13.01/5.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
