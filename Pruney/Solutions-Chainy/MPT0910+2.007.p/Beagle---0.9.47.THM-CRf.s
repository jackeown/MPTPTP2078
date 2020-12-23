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
% DateTime   : Thu Dec  3 10:10:00 EST 2020

% Result     : Theorem 10.65s
% Output     : CNFRefutation 10.86s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 309 expanded)
%              Number of leaves         :   35 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 ( 992 expanded)
%              Number of equality atoms :   79 ( 521 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_121,negated_conjecture,(
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

tff(f_97,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_395,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k7_mcart_1(A_127,B_128,C_129,D_130) = k2_mcart_1(D_130)
      | ~ m1_subset_1(D_130,k3_zfmisc_1(A_127,B_128,C_129))
      | k1_xboole_0 = C_129
      | k1_xboole_0 = B_128
      | k1_xboole_0 = A_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_410,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_395])).

tff(c_425,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_410])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( m1_subset_1(k7_mcart_1(A_20,B_21,C_22,D_23),C_22)
      | ~ m1_subset_1(D_23,k3_zfmisc_1(A_20,B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_432,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_16])).

tff(c_436,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_432])).

tff(c_122,plain,(
    ! [A_71,B_72,C_73] : k2_zfmisc_1(k2_zfmisc_1(A_71,B_72),C_73) = k3_zfmisc_1(A_71,B_72,C_73) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [A_71,B_72,C_73] : v1_relat_1(k3_zfmisc_1(A_71,B_72,C_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_6])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    ! [A_74,B_75] :
      ( k4_tarski(k1_mcart_1(A_74),k2_mcart_1(A_74)) = A_74
      | ~ r2_hidden(A_74,B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7039,plain,(
    ! [A_552,B_553] :
      ( k4_tarski(k1_mcart_1(A_552),k2_mcart_1(A_552)) = A_552
      | ~ v1_relat_1(B_553)
      | v1_xboole_0(B_553)
      | ~ m1_subset_1(A_552,B_553) ) ),
    inference(resolution,[status(thm)],[c_4,c_143])).

tff(c_7051,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_7039])).

tff(c_7061,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_7051])).

tff(c_7062,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7061])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7066,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7062,c_2])).

tff(c_24,plain,(
    ! [A_29,B_30,C_31] :
      ( k3_zfmisc_1(A_29,B_30,C_31) != k1_xboole_0
      | k1_xboole_0 = C_31
      | k1_xboole_0 = B_30
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7091,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7066,c_24])).

tff(c_7106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_7091])).

tff(c_7107,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7061])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( m1_subset_1(k6_mcart_1(A_16,B_17,C_18,D_19),B_17)
      | ~ m1_subset_1(D_19,k3_zfmisc_1(A_16,B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( m1_subset_1(k5_mcart_1(A_12,B_13,C_14,D_15),A_12)
      | ~ m1_subset_1(D_15,k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_454,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k6_mcart_1(A_133,B_134,C_135,D_136) = k2_mcart_1(k1_mcart_1(D_136))
      | ~ m1_subset_1(D_136,k3_zfmisc_1(A_133,B_134,C_135))
      | k1_xboole_0 = C_135
      | k1_xboole_0 = B_134
      | k1_xboole_0 = A_133 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_469,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_454])).

tff(c_484,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_469])).

tff(c_553,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k5_mcart_1(A_139,B_140,C_141,D_142) = k1_mcart_1(k1_mcart_1(D_142))
      | ~ m1_subset_1(D_142,k3_zfmisc_1(A_139,B_140,C_141))
      | k1_xboole_0 = C_141
      | k1_xboole_0 = B_140
      | k1_xboole_0 = A_139 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_568,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_553])).

tff(c_583,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_568])).

tff(c_7108,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7061])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k3_zfmisc_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden(k1_mcart_1(A_65),B_66)
      | ~ r2_hidden(A_65,k2_zfmisc_1(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6915,plain,(
    ! [A_541,B_542,C_543] :
      ( r2_hidden(k1_mcart_1(A_541),B_542)
      | v1_xboole_0(k2_zfmisc_1(B_542,C_543))
      | ~ m1_subset_1(A_541,k2_zfmisc_1(B_542,C_543)) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_6932,plain,(
    ! [A_541,A_9,B_10,C_11] :
      ( r2_hidden(k1_mcart_1(A_541),k2_zfmisc_1(A_9,B_10))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11))
      | ~ m1_subset_1(A_541,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_6915])).

tff(c_10838,plain,(
    ! [A_750,A_751,B_752,C_753] :
      ( r2_hidden(k1_mcart_1(A_750),k2_zfmisc_1(A_751,B_752))
      | v1_xboole_0(k3_zfmisc_1(A_751,B_752,C_753))
      | ~ m1_subset_1(A_750,k3_zfmisc_1(A_751,B_752,C_753)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6932])).

tff(c_10851,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_10838])).

tff(c_10864,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_7108,c_10851])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( k4_tarski(k1_mcart_1(A_27),k2_mcart_1(A_27)) = A_27
      | ~ r2_hidden(A_27,B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10869,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10864,c_22])).

tff(c_10876,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_484,c_583,c_10869])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_tarski(k4_tarski(A_6,B_7),C_8) = k3_mcart_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11037,plain,(
    ! [C_762] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_762) = k4_tarski(k1_mcart_1('#skF_5'),C_762) ),
    inference(superposition,[status(thm),theory(equality)],[c_10876,c_8])).

tff(c_46,plain,(
    ! [G_48,F_44,H_50] :
      ( G_48 = '#skF_4'
      | k3_mcart_1(F_44,G_48,H_50) != '#skF_5'
      | ~ m1_subset_1(H_50,'#skF_3')
      | ~ m1_subset_1(G_48,'#skF_2')
      | ~ m1_subset_1(F_44,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_11044,plain,(
    ! [C_762] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_762) != '#skF_5'
      | ~ m1_subset_1(C_762,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11037,c_46])).

tff(c_11050,plain,(
    ! [C_762] :
      ( k4_tarski(k1_mcart_1('#skF_5'),C_762) != '#skF_5'
      | ~ m1_subset_1(C_762,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_11044])).

tff(c_11394,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_11050])).

tff(c_11397,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_11394])).

tff(c_11401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_11397])).

tff(c_11402,plain,(
    ! [C_762] :
      ( ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | k4_tarski(k1_mcart_1('#skF_5'),C_762) != '#skF_5'
      | ~ m1_subset_1(C_762,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_11050])).

tff(c_11632,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_11402])).

tff(c_11635,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_11632])).

tff(c_11639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_11635])).

tff(c_11645,plain,(
    ! [C_795] :
      ( k4_tarski(k1_mcart_1('#skF_5'),C_795) != '#skF_5'
      | ~ m1_subset_1(C_795,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_11402])).

tff(c_11648,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7107,c_11645])).

tff(c_11652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_11648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.65/4.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.65/4.02  
% 10.65/4.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.65/4.02  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.65/4.02  
% 10.65/4.02  %Foreground sorts:
% 10.65/4.02  
% 10.65/4.02  
% 10.65/4.02  %Background operators:
% 10.65/4.02  
% 10.65/4.02  
% 10.65/4.02  %Foreground operators:
% 10.65/4.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.65/4.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.65/4.02  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.65/4.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.65/4.02  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 10.65/4.02  tff('#skF_5', type, '#skF_5': $i).
% 10.65/4.02  tff('#skF_2', type, '#skF_2': $i).
% 10.65/4.02  tff('#skF_3', type, '#skF_3': $i).
% 10.65/4.02  tff('#skF_1', type, '#skF_1': $i).
% 10.65/4.02  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 10.65/4.02  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 10.65/4.02  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 10.65/4.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.65/4.02  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 10.65/4.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.65/4.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.65/4.02  tff('#skF_4', type, '#skF_4': $i).
% 10.65/4.02  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 10.65/4.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.65/4.02  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 10.65/4.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.65/4.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.65/4.02  
% 10.86/4.04  tff(f_121, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 10.86/4.04  tff(f_97, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 10.86/4.04  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 10.86/4.04  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 10.86/4.04  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.86/4.04  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.86/4.04  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 10.86/4.04  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.86/4.04  tff(f_77, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 10.86/4.04  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 10.86/4.04  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 10.86/4.04  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 10.86/4.04  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 10.86/4.04  tff(c_48, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.86/4.04  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.86/4.04  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.86/4.04  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.86/4.04  tff(c_395, plain, (![A_127, B_128, C_129, D_130]: (k7_mcart_1(A_127, B_128, C_129, D_130)=k2_mcart_1(D_130) | ~m1_subset_1(D_130, k3_zfmisc_1(A_127, B_128, C_129)) | k1_xboole_0=C_129 | k1_xboole_0=B_128 | k1_xboole_0=A_127)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.86/4.04  tff(c_410, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_395])).
% 10.86/4.04  tff(c_425, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_410])).
% 10.86/4.04  tff(c_16, plain, (![A_20, B_21, C_22, D_23]: (m1_subset_1(k7_mcart_1(A_20, B_21, C_22, D_23), C_22) | ~m1_subset_1(D_23, k3_zfmisc_1(A_20, B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.86/4.04  tff(c_432, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_16])).
% 10.86/4.04  tff(c_436, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_432])).
% 10.86/4.04  tff(c_122, plain, (![A_71, B_72, C_73]: (k2_zfmisc_1(k2_zfmisc_1(A_71, B_72), C_73)=k3_zfmisc_1(A_71, B_72, C_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.86/4.04  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.86/4.04  tff(c_134, plain, (![A_71, B_72, C_73]: (v1_relat_1(k3_zfmisc_1(A_71, B_72, C_73)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_6])).
% 10.86/4.04  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.86/4.04  tff(c_143, plain, (![A_74, B_75]: (k4_tarski(k1_mcart_1(A_74), k2_mcart_1(A_74))=A_74 | ~r2_hidden(A_74, B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.86/4.04  tff(c_7039, plain, (![A_552, B_553]: (k4_tarski(k1_mcart_1(A_552), k2_mcart_1(A_552))=A_552 | ~v1_relat_1(B_553) | v1_xboole_0(B_553) | ~m1_subset_1(A_552, B_553))), inference(resolution, [status(thm)], [c_4, c_143])).
% 10.86/4.04  tff(c_7051, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_7039])).
% 10.86/4.04  tff(c_7061, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_7051])).
% 10.86/4.04  tff(c_7062, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_7061])).
% 10.86/4.04  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.86/4.04  tff(c_7066, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_7062, c_2])).
% 10.86/4.04  tff(c_24, plain, (![A_29, B_30, C_31]: (k3_zfmisc_1(A_29, B_30, C_31)!=k1_xboole_0 | k1_xboole_0=C_31 | k1_xboole_0=B_30 | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.86/4.04  tff(c_7091, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7066, c_24])).
% 10.86/4.04  tff(c_7106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_7091])).
% 10.86/4.04  tff(c_7107, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_7061])).
% 10.86/4.04  tff(c_14, plain, (![A_16, B_17, C_18, D_19]: (m1_subset_1(k6_mcart_1(A_16, B_17, C_18, D_19), B_17) | ~m1_subset_1(D_19, k3_zfmisc_1(A_16, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.86/4.04  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (m1_subset_1(k5_mcart_1(A_12, B_13, C_14, D_15), A_12) | ~m1_subset_1(D_15, k3_zfmisc_1(A_12, B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.86/4.04  tff(c_38, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.86/4.04  tff(c_454, plain, (![A_133, B_134, C_135, D_136]: (k6_mcart_1(A_133, B_134, C_135, D_136)=k2_mcart_1(k1_mcart_1(D_136)) | ~m1_subset_1(D_136, k3_zfmisc_1(A_133, B_134, C_135)) | k1_xboole_0=C_135 | k1_xboole_0=B_134 | k1_xboole_0=A_133)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.86/4.04  tff(c_469, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_454])).
% 10.86/4.04  tff(c_484, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_469])).
% 10.86/4.04  tff(c_553, plain, (![A_139, B_140, C_141, D_142]: (k5_mcart_1(A_139, B_140, C_141, D_142)=k1_mcart_1(k1_mcart_1(D_142)) | ~m1_subset_1(D_142, k3_zfmisc_1(A_139, B_140, C_141)) | k1_xboole_0=C_141 | k1_xboole_0=B_140 | k1_xboole_0=A_139)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.86/4.04  tff(c_568, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_553])).
% 10.86/4.04  tff(c_583, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_568])).
% 10.86/4.04  tff(c_7108, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_7061])).
% 10.86/4.04  tff(c_10, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k3_zfmisc_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.86/4.04  tff(c_102, plain, (![A_65, B_66, C_67]: (r2_hidden(k1_mcart_1(A_65), B_66) | ~r2_hidden(A_65, k2_zfmisc_1(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.86/4.04  tff(c_6915, plain, (![A_541, B_542, C_543]: (r2_hidden(k1_mcart_1(A_541), B_542) | v1_xboole_0(k2_zfmisc_1(B_542, C_543)) | ~m1_subset_1(A_541, k2_zfmisc_1(B_542, C_543)))), inference(resolution, [status(thm)], [c_4, c_102])).
% 10.86/4.04  tff(c_6932, plain, (![A_541, A_9, B_10, C_11]: (r2_hidden(k1_mcart_1(A_541), k2_zfmisc_1(A_9, B_10)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)) | ~m1_subset_1(A_541, k3_zfmisc_1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_6915])).
% 10.86/4.04  tff(c_10838, plain, (![A_750, A_751, B_752, C_753]: (r2_hidden(k1_mcart_1(A_750), k2_zfmisc_1(A_751, B_752)) | v1_xboole_0(k3_zfmisc_1(A_751, B_752, C_753)) | ~m1_subset_1(A_750, k3_zfmisc_1(A_751, B_752, C_753)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6932])).
% 10.86/4.04  tff(c_10851, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_10838])).
% 10.86/4.04  tff(c_10864, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_7108, c_10851])).
% 10.86/4.04  tff(c_22, plain, (![A_27, B_28]: (k4_tarski(k1_mcart_1(A_27), k2_mcart_1(A_27))=A_27 | ~r2_hidden(A_27, B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.86/4.04  tff(c_10869, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10864, c_22])).
% 10.86/4.04  tff(c_10876, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_484, c_583, c_10869])).
% 10.86/4.04  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_tarski(k4_tarski(A_6, B_7), C_8)=k3_mcart_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.86/4.04  tff(c_11037, plain, (![C_762]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_762)=k4_tarski(k1_mcart_1('#skF_5'), C_762))), inference(superposition, [status(thm), theory('equality')], [c_10876, c_8])).
% 10.86/4.04  tff(c_46, plain, (![G_48, F_44, H_50]: (G_48='#skF_4' | k3_mcart_1(F_44, G_48, H_50)!='#skF_5' | ~m1_subset_1(H_50, '#skF_3') | ~m1_subset_1(G_48, '#skF_2') | ~m1_subset_1(F_44, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.86/4.04  tff(c_11044, plain, (![C_762]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_762)!='#skF_5' | ~m1_subset_1(C_762, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11037, c_46])).
% 10.86/4.04  tff(c_11050, plain, (![C_762]: (k4_tarski(k1_mcart_1('#skF_5'), C_762)!='#skF_5' | ~m1_subset_1(C_762, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_38, c_11044])).
% 10.86/4.04  tff(c_11394, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_11050])).
% 10.86/4.04  tff(c_11397, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_11394])).
% 10.86/4.04  tff(c_11401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_11397])).
% 10.86/4.04  tff(c_11402, plain, (![C_762]: (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | k4_tarski(k1_mcart_1('#skF_5'), C_762)!='#skF_5' | ~m1_subset_1(C_762, '#skF_3'))), inference(splitRight, [status(thm)], [c_11050])).
% 10.86/4.04  tff(c_11632, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_11402])).
% 10.86/4.04  tff(c_11635, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_11632])).
% 10.86/4.04  tff(c_11639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_11635])).
% 10.86/4.04  tff(c_11645, plain, (![C_795]: (k4_tarski(k1_mcart_1('#skF_5'), C_795)!='#skF_5' | ~m1_subset_1(C_795, '#skF_3'))), inference(splitRight, [status(thm)], [c_11402])).
% 10.86/4.04  tff(c_11648, plain, (~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7107, c_11645])).
% 10.86/4.04  tff(c_11652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_436, c_11648])).
% 10.86/4.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.86/4.04  
% 10.86/4.04  Inference rules
% 10.86/4.04  ----------------------
% 10.86/4.04  #Ref     : 0
% 10.86/4.04  #Sup     : 3267
% 10.86/4.04  #Fact    : 0
% 10.86/4.04  #Define  : 0
% 10.86/4.04  #Split   : 16
% 10.86/4.04  #Chain   : 0
% 10.86/4.04  #Close   : 0
% 10.86/4.04  
% 10.86/4.04  Ordering : KBO
% 10.86/4.04  
% 10.86/4.04  Simplification rules
% 10.86/4.04  ----------------------
% 10.86/4.04  #Subsume      : 591
% 10.86/4.04  #Demod        : 647
% 10.86/4.04  #Tautology    : 322
% 10.86/4.04  #SimpNegUnit  : 14
% 10.86/4.04  #BackRed      : 4
% 10.86/4.04  
% 10.86/4.04  #Partial instantiations: 0
% 10.86/4.04  #Strategies tried      : 1
% 10.86/4.04  
% 10.86/4.04  Timing (in seconds)
% 10.86/4.04  ----------------------
% 10.86/4.04  Preprocessing        : 0.33
% 10.86/4.04  Parsing              : 0.18
% 10.86/4.04  CNF conversion       : 0.02
% 10.86/4.04  Main loop            : 2.92
% 10.86/4.04  Inferencing          : 0.77
% 10.86/4.04  Reduction            : 0.61
% 10.86/4.04  Demodulation         : 0.42
% 10.86/4.04  BG Simplification    : 0.10
% 10.86/4.05  Subsumption          : 1.26
% 10.86/4.05  Abstraction          : 0.13
% 10.86/4.05  MUC search           : 0.00
% 10.86/4.05  Cooper               : 0.00
% 10.86/4.05  Total                : 3.29
% 10.86/4.05  Index Insertion      : 0.00
% 10.86/4.05  Index Deletion       : 0.00
% 10.86/4.05  Index Matching       : 0.00
% 10.86/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
