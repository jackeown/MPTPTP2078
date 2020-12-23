%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:00 EST 2020

% Result     : Theorem 22.61s
% Output     : CNFRefutation 22.61s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 286 expanded)
%              Number of leaves         :   32 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  186 ( 883 expanded)
%              Number of equality atoms :   99 ( 471 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_457,plain,(
    ! [A_143,B_144,C_145,D_146] :
      ( k7_mcart_1(A_143,B_144,C_145,D_146) = k2_mcart_1(D_146)
      | ~ m1_subset_1(D_146,k3_zfmisc_1(A_143,B_144,C_145))
      | k1_xboole_0 = C_145
      | k1_xboole_0 = B_144
      | k1_xboole_0 = A_143 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_513,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_457])).

tff(c_530,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_513])).

tff(c_22,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(k7_mcart_1(A_22,B_23,C_24,D_25),C_24)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_534,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_22])).

tff(c_538,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_534])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_389,plain,(
    ! [C_134,A_135,B_136] :
      ( k4_tarski(k1_mcart_1(C_134),k2_mcart_1(C_134)) = C_134
      | ~ m1_subset_1(C_134,k2_zfmisc_1(A_135,B_136))
      | k1_xboole_0 = B_136
      | k1_xboole_0 = A_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22520,plain,(
    ! [C_1102,A_1103,B_1104,C_1105] :
      ( k4_tarski(k1_mcart_1(C_1102),k2_mcart_1(C_1102)) = C_1102
      | ~ m1_subset_1(C_1102,k3_zfmisc_1(A_1103,B_1104,C_1105))
      | k1_xboole_0 = C_1105
      | k2_zfmisc_1(A_1103,B_1104) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_389])).

tff(c_22629,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_22520])).

tff(c_22669,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_22629])).

tff(c_22670,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22669])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22690,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_22670,c_4])).

tff(c_22701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_22690])).

tff(c_22702,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_22669])).

tff(c_36,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_20530,plain,(
    ! [A_965,B_966,C_967,D_968] :
      ( k5_mcart_1(A_965,B_966,C_967,D_968) = k1_mcart_1(k1_mcart_1(D_968))
      | ~ m1_subset_1(D_968,k3_zfmisc_1(A_965,B_966,C_967))
      | k1_xboole_0 = C_967
      | k1_xboole_0 = B_966
      | k1_xboole_0 = A_965 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20610,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_20530])).

tff(c_20633,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_20610])).

tff(c_22703,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22669])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    ! [A_64,C_65,B_66] :
      ( r2_hidden(k2_mcart_1(A_64),C_65)
      | ~ r2_hidden(A_64,k2_zfmisc_1(B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_21973,plain,(
    ! [A_1076,C_1077,B_1078] :
      ( r2_hidden(k2_mcart_1(A_1076),C_1077)
      | v1_xboole_0(k2_zfmisc_1(B_1078,C_1077))
      | ~ m1_subset_1(A_1076,k2_zfmisc_1(B_1078,C_1077)) ) ),
    inference(resolution,[status(thm)],[c_12,c_88])).

tff(c_22074,plain,(
    ! [A_1076,C_13,A_11,B_12] :
      ( r2_hidden(k2_mcart_1(A_1076),C_13)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13))
      | ~ m1_subset_1(A_1076,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_21973])).

tff(c_28779,plain,(
    ! [A_1336,C_1337,A_1338,B_1339] :
      ( r2_hidden(k2_mcart_1(A_1336),C_1337)
      | v1_xboole_0(k3_zfmisc_1(A_1338,B_1339,C_1337))
      | ~ m1_subset_1(A_1336,k3_zfmisc_1(A_1338,B_1339,C_1337)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22074])).

tff(c_29054,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_28779])).

tff(c_29055,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_29054])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29059,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29055,c_2])).

tff(c_111,plain,(
    ! [A_70,B_71,C_72] : k2_zfmisc_1(k2_zfmisc_1(A_70,B_71),C_72) = k3_zfmisc_1(A_70,B_71,C_72) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [C_72,A_70,B_71] :
      ( k1_xboole_0 = C_72
      | k2_zfmisc_1(A_70,B_71) = k1_xboole_0
      | k3_zfmisc_1(A_70,B_71,C_72) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_4])).

tff(c_29097,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_29059,c_122])).

tff(c_29134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22703,c_38,c_29097])).

tff(c_29136,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_29054])).

tff(c_220,plain,(
    ! [A_89,B_90,C_91] :
      ( r2_hidden(k1_mcart_1(A_89),B_90)
      | ~ r2_hidden(A_89,k2_zfmisc_1(B_90,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22245,plain,(
    ! [A_1089,B_1090,C_1091] :
      ( r2_hidden(k1_mcart_1(A_1089),B_1090)
      | v1_xboole_0(k2_zfmisc_1(B_1090,C_1091))
      | ~ m1_subset_1(A_1089,k2_zfmisc_1(B_1090,C_1091)) ) ),
    inference(resolution,[status(thm)],[c_12,c_220])).

tff(c_22346,plain,(
    ! [A_1089,A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_1089),k2_zfmisc_1(A_11,B_12))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13))
      | ~ m1_subset_1(A_1089,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22245])).

tff(c_29532,plain,(
    ! [A_1360,A_1361,B_1362,C_1363] :
      ( r2_hidden(k1_mcart_1(A_1360),k2_zfmisc_1(A_1361,B_1362))
      | v1_xboole_0(k3_zfmisc_1(A_1361,B_1362,C_1363))
      | ~ m1_subset_1(A_1360,k3_zfmisc_1(A_1361,B_1362,C_1363)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_22346])).

tff(c_29737,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_29532])).

tff(c_29809,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_29136,c_29737])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k1_mcart_1(A_26),B_27)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_29811,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_29809,c_26])).

tff(c_29818,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20633,c_29811])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29838,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_29818,c_10])).

tff(c_570,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k6_mcart_1(A_153,B_154,C_155,D_156) = k2_mcart_1(k1_mcart_1(D_156))
      | ~ m1_subset_1(D_156,k3_zfmisc_1(A_153,B_154,C_155))
      | k1_xboole_0 = C_155
      | k1_xboole_0 = B_154
      | k1_xboole_0 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_638,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_570])).

tff(c_658,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_638])).

tff(c_24,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(k2_mcart_1(A_26),C_28)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_29813,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_29809,c_24])).

tff(c_29820,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_29813])).

tff(c_29852,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_29820,c_10])).

tff(c_29821,plain,(
    m1_subset_1(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_29809,c_10])).

tff(c_28,plain,(
    ! [C_32,A_29,B_30] :
      ( k4_tarski(k1_mcart_1(C_32),k2_mcart_1(C_32)) = C_32
      | ~ m1_subset_1(C_32,k2_zfmisc_1(A_29,B_30))
      | k1_xboole_0 = B_30
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_29827,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_29821,c_28])).

tff(c_29833,plain,
    ( k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_20633,c_29827])).

tff(c_29834,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_29833])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40440,plain,(
    ! [C_1771] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_1771) = k4_tarski(k1_mcart_1('#skF_5'),C_1771) ),
    inference(superposition,[status(thm),theory(equality)],[c_29834,c_14])).

tff(c_44,plain,(
    ! [G_49,F_45,H_51] :
      ( G_49 = '#skF_4'
      | k3_mcart_1(F_45,G_49,H_51) != '#skF_5'
      | ~ m1_subset_1(H_51,'#skF_3')
      | ~ m1_subset_1(G_49,'#skF_2')
      | ~ m1_subset_1(F_45,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40447,plain,(
    ! [C_1771] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_1771) != '#skF_5'
      | ~ m1_subset_1(C_1771,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40440,c_44])).

tff(c_40454,plain,(
    ! [C_1771] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_1771) != '#skF_5'
      | ~ m1_subset_1(C_1771,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29838,c_29852,c_40447])).

tff(c_40457,plain,(
    ! [C_1772] :
      ( k4_tarski(k1_mcart_1('#skF_5'),C_1772) != '#skF_5'
      | ~ m1_subset_1(C_1772,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_40454])).

tff(c_40460,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22702,c_40457])).

tff(c_40464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_40460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.61/13.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.61/13.38  
% 22.61/13.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.61/13.38  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.61/13.38  
% 22.61/13.38  %Foreground sorts:
% 22.61/13.38  
% 22.61/13.38  
% 22.61/13.38  %Background operators:
% 22.61/13.38  
% 22.61/13.38  
% 22.61/13.38  %Foreground operators:
% 22.61/13.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.61/13.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.61/13.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 22.61/13.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.61/13.38  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 22.61/13.38  tff('#skF_5', type, '#skF_5': $i).
% 22.61/13.38  tff('#skF_2', type, '#skF_2': $i).
% 22.61/13.38  tff('#skF_3', type, '#skF_3': $i).
% 22.61/13.38  tff('#skF_1', type, '#skF_1': $i).
% 22.61/13.38  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 22.61/13.38  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 22.61/13.38  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 22.61/13.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.61/13.38  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 22.61/13.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.61/13.38  tff('#skF_4', type, '#skF_4': $i).
% 22.61/13.38  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 22.61/13.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.61/13.38  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 22.61/13.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.61/13.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.61/13.38  
% 22.61/13.40  tff(f_124, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 22.61/13.40  tff(f_100, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 22.61/13.40  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 22.61/13.40  tff(f_49, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 22.61/13.40  tff(f_80, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 22.61/13.40  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 22.61/13.40  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 22.61/13.40  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 22.61/13.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 22.61/13.40  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 22.61/13.40  tff(f_47, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 22.61/13.40  tff(c_46, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 22.61/13.40  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_124])).
% 22.61/13.40  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 22.61/13.40  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_124])).
% 22.61/13.40  tff(c_457, plain, (![A_143, B_144, C_145, D_146]: (k7_mcart_1(A_143, B_144, C_145, D_146)=k2_mcart_1(D_146) | ~m1_subset_1(D_146, k3_zfmisc_1(A_143, B_144, C_145)) | k1_xboole_0=C_145 | k1_xboole_0=B_144 | k1_xboole_0=A_143)), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.61/13.40  tff(c_513, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_457])).
% 22.61/13.40  tff(c_530, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_513])).
% 22.61/13.40  tff(c_22, plain, (![A_22, B_23, C_24, D_25]: (m1_subset_1(k7_mcart_1(A_22, B_23, C_24, D_25), C_24) | ~m1_subset_1(D_25, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.61/13.40  tff(c_534, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_530, c_22])).
% 22.61/13.40  tff(c_538, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_534])).
% 22.61/13.40  tff(c_16, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.61/13.40  tff(c_389, plain, (![C_134, A_135, B_136]: (k4_tarski(k1_mcart_1(C_134), k2_mcart_1(C_134))=C_134 | ~m1_subset_1(C_134, k2_zfmisc_1(A_135, B_136)) | k1_xboole_0=B_136 | k1_xboole_0=A_135)), inference(cnfTransformation, [status(thm)], [f_80])).
% 22.61/13.40  tff(c_22520, plain, (![C_1102, A_1103, B_1104, C_1105]: (k4_tarski(k1_mcart_1(C_1102), k2_mcart_1(C_1102))=C_1102 | ~m1_subset_1(C_1102, k3_zfmisc_1(A_1103, B_1104, C_1105)) | k1_xboole_0=C_1105 | k2_zfmisc_1(A_1103, B_1104)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_389])).
% 22.61/13.40  tff(c_22629, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_22520])).
% 22.61/13.40  tff(c_22669, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_38, c_22629])).
% 22.61/13.40  tff(c_22670, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22669])).
% 22.61/13.40  tff(c_4, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 22.61/13.40  tff(c_22690, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_22670, c_4])).
% 22.61/13.40  tff(c_22701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_22690])).
% 22.61/13.40  tff(c_22702, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_22669])).
% 22.61/13.40  tff(c_36, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 22.61/13.40  tff(c_20530, plain, (![A_965, B_966, C_967, D_968]: (k5_mcart_1(A_965, B_966, C_967, D_968)=k1_mcart_1(k1_mcart_1(D_968)) | ~m1_subset_1(D_968, k3_zfmisc_1(A_965, B_966, C_967)) | k1_xboole_0=C_967 | k1_xboole_0=B_966 | k1_xboole_0=A_965)), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.61/13.40  tff(c_20610, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_20530])).
% 22.61/13.40  tff(c_20633, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_20610])).
% 22.61/13.40  tff(c_22703, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_22669])).
% 22.61/13.40  tff(c_12, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.61/13.40  tff(c_88, plain, (![A_64, C_65, B_66]: (r2_hidden(k2_mcart_1(A_64), C_65) | ~r2_hidden(A_64, k2_zfmisc_1(B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.61/13.40  tff(c_21973, plain, (![A_1076, C_1077, B_1078]: (r2_hidden(k2_mcart_1(A_1076), C_1077) | v1_xboole_0(k2_zfmisc_1(B_1078, C_1077)) | ~m1_subset_1(A_1076, k2_zfmisc_1(B_1078, C_1077)))), inference(resolution, [status(thm)], [c_12, c_88])).
% 22.61/13.40  tff(c_22074, plain, (![A_1076, C_13, A_11, B_12]: (r2_hidden(k2_mcart_1(A_1076), C_13) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)) | ~m1_subset_1(A_1076, k3_zfmisc_1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_21973])).
% 22.61/13.40  tff(c_28779, plain, (![A_1336, C_1337, A_1338, B_1339]: (r2_hidden(k2_mcart_1(A_1336), C_1337) | v1_xboole_0(k3_zfmisc_1(A_1338, B_1339, C_1337)) | ~m1_subset_1(A_1336, k3_zfmisc_1(A_1338, B_1339, C_1337)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22074])).
% 22.61/13.40  tff(c_29054, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_28779])).
% 22.61/13.40  tff(c_29055, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_29054])).
% 22.61/13.40  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 22.61/13.40  tff(c_29059, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_29055, c_2])).
% 22.61/13.40  tff(c_111, plain, (![A_70, B_71, C_72]: (k2_zfmisc_1(k2_zfmisc_1(A_70, B_71), C_72)=k3_zfmisc_1(A_70, B_71, C_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 22.61/13.40  tff(c_122, plain, (![C_72, A_70, B_71]: (k1_xboole_0=C_72 | k2_zfmisc_1(A_70, B_71)=k1_xboole_0 | k3_zfmisc_1(A_70, B_71, C_72)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_111, c_4])).
% 22.61/13.40  tff(c_29097, plain, (k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_29059, c_122])).
% 22.61/13.40  tff(c_29134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22703, c_38, c_29097])).
% 22.61/13.40  tff(c_29136, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_29054])).
% 22.61/13.40  tff(c_220, plain, (![A_89, B_90, C_91]: (r2_hidden(k1_mcart_1(A_89), B_90) | ~r2_hidden(A_89, k2_zfmisc_1(B_90, C_91)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.61/13.40  tff(c_22245, plain, (![A_1089, B_1090, C_1091]: (r2_hidden(k1_mcart_1(A_1089), B_1090) | v1_xboole_0(k2_zfmisc_1(B_1090, C_1091)) | ~m1_subset_1(A_1089, k2_zfmisc_1(B_1090, C_1091)))), inference(resolution, [status(thm)], [c_12, c_220])).
% 22.61/13.40  tff(c_22346, plain, (![A_1089, A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_1089), k2_zfmisc_1(A_11, B_12)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)) | ~m1_subset_1(A_1089, k3_zfmisc_1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_22245])).
% 22.61/13.40  tff(c_29532, plain, (![A_1360, A_1361, B_1362, C_1363]: (r2_hidden(k1_mcart_1(A_1360), k2_zfmisc_1(A_1361, B_1362)) | v1_xboole_0(k3_zfmisc_1(A_1361, B_1362, C_1363)) | ~m1_subset_1(A_1360, k3_zfmisc_1(A_1361, B_1362, C_1363)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_22346])).
% 22.61/13.40  tff(c_29737, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_29532])).
% 22.61/13.40  tff(c_29809, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_29136, c_29737])).
% 22.61/13.40  tff(c_26, plain, (![A_26, B_27, C_28]: (r2_hidden(k1_mcart_1(A_26), B_27) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.61/13.40  tff(c_29811, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_29809, c_26])).
% 22.61/13.40  tff(c_29818, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20633, c_29811])).
% 22.61/13.40  tff(c_10, plain, (![A_4, B_5]: (m1_subset_1(A_4, B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 22.61/13.40  tff(c_29838, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_29818, c_10])).
% 22.61/13.40  tff(c_570, plain, (![A_153, B_154, C_155, D_156]: (k6_mcart_1(A_153, B_154, C_155, D_156)=k2_mcart_1(k1_mcart_1(D_156)) | ~m1_subset_1(D_156, k3_zfmisc_1(A_153, B_154, C_155)) | k1_xboole_0=C_155 | k1_xboole_0=B_154 | k1_xboole_0=A_153)), inference(cnfTransformation, [status(thm)], [f_100])).
% 22.61/13.40  tff(c_638, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_570])).
% 22.61/13.40  tff(c_658, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_638])).
% 22.61/13.40  tff(c_24, plain, (![A_26, C_28, B_27]: (r2_hidden(k2_mcart_1(A_26), C_28) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.61/13.40  tff(c_29813, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_29809, c_24])).
% 22.61/13.40  tff(c_29820, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_658, c_29813])).
% 22.61/13.40  tff(c_29852, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_29820, c_10])).
% 22.61/13.40  tff(c_29821, plain, (m1_subset_1(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_29809, c_10])).
% 22.61/13.40  tff(c_28, plain, (![C_32, A_29, B_30]: (k4_tarski(k1_mcart_1(C_32), k2_mcart_1(C_32))=C_32 | ~m1_subset_1(C_32, k2_zfmisc_1(A_29, B_30)) | k1_xboole_0=B_30 | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_80])).
% 22.61/13.40  tff(c_29827, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_29821, c_28])).
% 22.61/13.40  tff(c_29833, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_20633, c_29827])).
% 22.61/13.40  tff(c_29834, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_29833])).
% 22.61/13.40  tff(c_14, plain, (![A_8, B_9, C_10]: (k4_tarski(k4_tarski(A_8, B_9), C_10)=k3_mcart_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 22.61/13.40  tff(c_40440, plain, (![C_1771]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_1771)=k4_tarski(k1_mcart_1('#skF_5'), C_1771))), inference(superposition, [status(thm), theory('equality')], [c_29834, c_14])).
% 22.61/13.40  tff(c_44, plain, (![G_49, F_45, H_51]: (G_49='#skF_4' | k3_mcart_1(F_45, G_49, H_51)!='#skF_5' | ~m1_subset_1(H_51, '#skF_3') | ~m1_subset_1(G_49, '#skF_2') | ~m1_subset_1(F_45, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 22.61/13.40  tff(c_40447, plain, (![C_1771]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_1771)!='#skF_5' | ~m1_subset_1(C_1771, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_40440, c_44])).
% 22.61/13.40  tff(c_40454, plain, (![C_1771]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_1771)!='#skF_5' | ~m1_subset_1(C_1771, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_29838, c_29852, c_40447])).
% 22.61/13.40  tff(c_40457, plain, (![C_1772]: (k4_tarski(k1_mcart_1('#skF_5'), C_1772)!='#skF_5' | ~m1_subset_1(C_1772, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_40454])).
% 22.61/13.40  tff(c_40460, plain, (~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22702, c_40457])).
% 22.61/13.40  tff(c_40464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_538, c_40460])).
% 22.61/13.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.61/13.40  
% 22.61/13.40  Inference rules
% 22.61/13.40  ----------------------
% 22.61/13.40  #Ref     : 0
% 22.61/13.40  #Sup     : 10419
% 22.61/13.40  #Fact    : 0
% 22.61/13.40  #Define  : 0
% 22.61/13.40  #Split   : 12
% 22.61/13.40  #Chain   : 0
% 22.61/13.40  #Close   : 0
% 22.61/13.40  
% 22.61/13.40  Ordering : KBO
% 22.61/13.40  
% 22.61/13.40  Simplification rules
% 22.61/13.40  ----------------------
% 22.61/13.40  #Subsume      : 1437
% 22.61/13.40  #Demod        : 1737
% 22.61/13.40  #Tautology    : 575
% 22.61/13.40  #SimpNegUnit  : 28
% 22.61/13.40  #BackRed      : 4
% 22.61/13.40  
% 22.61/13.40  #Partial instantiations: 0
% 22.61/13.40  #Strategies tried      : 1
% 22.61/13.40  
% 22.61/13.40  Timing (in seconds)
% 22.61/13.40  ----------------------
% 22.61/13.40  Preprocessing        : 0.36
% 22.61/13.40  Parsing              : 0.19
% 22.61/13.40  CNF conversion       : 0.03
% 22.61/13.40  Main loop            : 12.25
% 22.61/13.40  Inferencing          : 2.09
% 22.61/13.40  Reduction            : 1.73
% 22.61/13.40  Demodulation         : 1.17
% 22.61/13.40  BG Simplification    : 0.29
% 22.61/13.40  Subsumption          : 7.50
% 22.61/13.40  Abstraction          : 0.48
% 22.61/13.40  MUC search           : 0.00
% 22.61/13.40  Cooper               : 0.00
% 22.61/13.40  Total                : 12.64
% 22.61/13.40  Index Insertion      : 0.00
% 22.61/13.40  Index Deletion       : 0.00
% 22.61/13.40  Index Matching       : 0.00
% 22.61/13.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
