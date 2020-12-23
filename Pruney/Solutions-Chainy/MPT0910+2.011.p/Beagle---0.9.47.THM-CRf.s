%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:00 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.66s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 253 expanded)
%              Number of leaves         :   34 ( 103 expanded)
%              Depth                    :   14
%              Number of atoms          :  163 ( 753 expanded)
%              Number of equality atoms :   79 ( 374 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

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

tff(c_338,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k7_mcart_1(A_125,B_126,C_127,D_128) = k2_mcart_1(D_128)
      | ~ m1_subset_1(D_128,k3_zfmisc_1(A_125,B_126,C_127))
      | k1_xboole_0 = C_127
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_377,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_338])).

tff(c_398,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_377])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( m1_subset_1(k7_mcart_1(A_18,B_19,C_20,D_21),C_20)
      | ~ m1_subset_1(D_21,k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_405,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_16])).

tff(c_409,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_405])).

tff(c_107,plain,(
    ! [A_65,B_66,C_67] : k2_zfmisc_1(k2_zfmisc_1(A_65,B_66),C_67) = k3_zfmisc_1(A_65,B_66,C_67) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [A_65,B_66,C_67] : v1_relat_1(k3_zfmisc_1(A_65,B_66,C_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_8])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_237,plain,(
    ! [A_95,B_96] :
      ( k4_tarski(k1_mcart_1(A_95),k2_mcart_1(A_95)) = A_95
      | ~ r2_hidden(A_95,B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9504,plain,(
    ! [A_602,B_603] :
      ( k4_tarski(k1_mcart_1(A_602),k2_mcart_1(A_602)) = A_602
      | ~ v1_relat_1(B_603)
      | v1_xboole_0(B_603)
      | ~ m1_subset_1(A_602,B_603) ) ),
    inference(resolution,[status(thm)],[c_6,c_237])).

tff(c_9546,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_9504])).

tff(c_9577,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_9546])).

tff(c_9578,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9577])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_9582,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9578,c_2])).

tff(c_24,plain,(
    ! [A_27,B_28,C_29] :
      ( k3_zfmisc_1(A_27,B_28,C_29) != k1_xboole_0
      | k1_xboole_0 = C_29
      | k1_xboole_0 = B_28
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9609,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_9582,c_24])).

tff(c_9624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_9609])).

tff(c_9625,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9577])).

tff(c_38,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_431,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k5_mcart_1(A_131,B_132,C_133,D_134) = k1_mcart_1(k1_mcart_1(D_134))
      | ~ m1_subset_1(D_134,k3_zfmisc_1(A_131,B_132,C_133))
      | k1_xboole_0 = C_133
      | k1_xboole_0 = B_132
      | k1_xboole_0 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_470,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_431])).

tff(c_491,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_470])).

tff(c_9626,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9577])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [A_77,B_78,C_79] :
      ( r2_hidden(k1_mcart_1(A_77),B_78)
      | ~ r2_hidden(A_77,k2_zfmisc_1(B_78,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9651,plain,(
    ! [A_605,B_606,C_607] :
      ( r2_hidden(k1_mcart_1(A_605),B_606)
      | v1_xboole_0(k2_zfmisc_1(B_606,C_607))
      | ~ m1_subset_1(A_605,k2_zfmisc_1(B_606,C_607)) ) ),
    inference(resolution,[status(thm)],[c_6,c_151])).

tff(c_9706,plain,(
    ! [A_605,A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_605),k2_zfmisc_1(A_11,B_12))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13))
      | ~ m1_subset_1(A_605,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_9651])).

tff(c_13196,plain,(
    ! [A_765,A_766,B_767,C_768] :
      ( r2_hidden(k1_mcart_1(A_765),k2_zfmisc_1(A_766,B_767))
      | v1_xboole_0(k3_zfmisc_1(A_766,B_767,C_768))
      | ~ m1_subset_1(A_765,k3_zfmisc_1(A_766,B_767,C_768)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_9706])).

tff(c_13314,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_13196])).

tff(c_13362,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_9626,c_13314])).

tff(c_20,plain,(
    ! [A_22,B_23,C_24] :
      ( r2_hidden(k1_mcart_1(A_22),B_23)
      | ~ r2_hidden(A_22,k2_zfmisc_1(B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13369,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13362,c_20])).

tff(c_13379,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_13369])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_13402,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13379,c_4])).

tff(c_559,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k6_mcart_1(A_141,B_142,C_143,D_144) = k2_mcart_1(k1_mcart_1(D_144))
      | ~ m1_subset_1(D_144,k3_zfmisc_1(A_141,B_142,C_143))
      | k1_xboole_0 = C_143
      | k1_xboole_0 = B_142
      | k1_xboole_0 = A_141 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_598,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_559])).

tff(c_619,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_598])).

tff(c_18,plain,(
    ! [A_22,C_24,B_23] :
      ( r2_hidden(k2_mcart_1(A_22),C_24)
      | ~ r2_hidden(A_22,k2_zfmisc_1(B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13371,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_13362,c_18])).

tff(c_13381,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_13371])).

tff(c_13409,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_13381,c_4])).

tff(c_22,plain,(
    ! [A_25,B_26] :
      ( k4_tarski(k1_mcart_1(A_25),k2_mcart_1(A_25)) = A_25
      | ~ r2_hidden(A_25,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_13367,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_13362,c_22])).

tff(c_13377,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_491,c_619,c_13367])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k4_tarski(k4_tarski(A_8,B_9),C_10) = k3_mcart_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16286,plain,(
    ! [C_878] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_878) = k4_tarski(k1_mcart_1('#skF_5'),C_878) ),
    inference(superposition,[status(thm),theory(equality)],[c_13377,c_10])).

tff(c_46,plain,(
    ! [G_46,F_42,H_48] :
      ( G_46 = '#skF_4'
      | k3_mcart_1(F_42,G_46,H_48) != '#skF_5'
      | ~ m1_subset_1(H_48,'#skF_3')
      | ~ m1_subset_1(G_46,'#skF_2')
      | ~ m1_subset_1(F_42,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16293,plain,(
    ! [C_878] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_878) != '#skF_5'
      | ~ m1_subset_1(C_878,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16286,c_46])).

tff(c_16300,plain,(
    ! [C_878] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_878) != '#skF_5'
      | ~ m1_subset_1(C_878,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13402,c_13409,c_16293])).

tff(c_16303,plain,(
    ! [C_879] :
      ( k4_tarski(k1_mcart_1('#skF_5'),C_879) != '#skF_5'
      | ~ m1_subset_1(C_879,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_16300])).

tff(c_16306,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9625,c_16303])).

tff(c_16310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_16306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.62/4.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.62/4.84  
% 11.62/4.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.62/4.84  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.62/4.84  
% 11.62/4.84  %Foreground sorts:
% 11.62/4.84  
% 11.62/4.84  
% 11.62/4.84  %Background operators:
% 11.62/4.84  
% 11.62/4.84  
% 11.62/4.84  %Foreground operators:
% 11.62/4.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.62/4.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.62/4.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.62/4.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.62/4.84  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 11.62/4.84  tff('#skF_5', type, '#skF_5': $i).
% 11.62/4.84  tff('#skF_2', type, '#skF_2': $i).
% 11.62/4.84  tff('#skF_3', type, '#skF_3': $i).
% 11.62/4.84  tff('#skF_1', type, '#skF_1': $i).
% 11.62/4.84  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 11.62/4.84  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 11.62/4.84  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 11.62/4.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.62/4.84  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 11.62/4.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.62/4.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.62/4.84  tff('#skF_4', type, '#skF_4': $i).
% 11.62/4.84  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 11.62/4.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.62/4.84  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 11.62/4.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.62/4.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.62/4.84  
% 11.66/4.86  tff(f_121, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_mcart_1)).
% 11.66/4.86  tff(f_97, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 11.66/4.86  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 11.66/4.86  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 11.66/4.86  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.66/4.86  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.66/4.86  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 11.66/4.86  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.66/4.86  tff(f_77, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 11.66/4.86  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 11.66/4.86  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 11.66/4.86  tff(f_43, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 11.66/4.86  tff(c_48, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.66/4.86  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.66/4.86  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.66/4.86  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.66/4.86  tff(c_338, plain, (![A_125, B_126, C_127, D_128]: (k7_mcart_1(A_125, B_126, C_127, D_128)=k2_mcart_1(D_128) | ~m1_subset_1(D_128, k3_zfmisc_1(A_125, B_126, C_127)) | k1_xboole_0=C_127 | k1_xboole_0=B_126 | k1_xboole_0=A_125)), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.66/4.86  tff(c_377, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_338])).
% 11.66/4.86  tff(c_398, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_377])).
% 11.66/4.86  tff(c_16, plain, (![A_18, B_19, C_20, D_21]: (m1_subset_1(k7_mcart_1(A_18, B_19, C_20, D_21), C_20) | ~m1_subset_1(D_21, k3_zfmisc_1(A_18, B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.66/4.86  tff(c_405, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_398, c_16])).
% 11.66/4.86  tff(c_409, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_405])).
% 11.66/4.86  tff(c_107, plain, (![A_65, B_66, C_67]: (k2_zfmisc_1(k2_zfmisc_1(A_65, B_66), C_67)=k3_zfmisc_1(A_65, B_66, C_67))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.66/4.86  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.66/4.86  tff(c_117, plain, (![A_65, B_66, C_67]: (v1_relat_1(k3_zfmisc_1(A_65, B_66, C_67)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_8])).
% 11.66/4.86  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.66/4.86  tff(c_237, plain, (![A_95, B_96]: (k4_tarski(k1_mcart_1(A_95), k2_mcart_1(A_95))=A_95 | ~r2_hidden(A_95, B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.66/4.86  tff(c_9504, plain, (![A_602, B_603]: (k4_tarski(k1_mcart_1(A_602), k2_mcart_1(A_602))=A_602 | ~v1_relat_1(B_603) | v1_xboole_0(B_603) | ~m1_subset_1(A_602, B_603))), inference(resolution, [status(thm)], [c_6, c_237])).
% 11.66/4.86  tff(c_9546, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_9504])).
% 11.66/4.86  tff(c_9577, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_9546])).
% 11.66/4.86  tff(c_9578, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_9577])).
% 11.66/4.86  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.66/4.86  tff(c_9582, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_9578, c_2])).
% 11.66/4.86  tff(c_24, plain, (![A_27, B_28, C_29]: (k3_zfmisc_1(A_27, B_28, C_29)!=k1_xboole_0 | k1_xboole_0=C_29 | k1_xboole_0=B_28 | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.66/4.86  tff(c_9609, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_9582, c_24])).
% 11.66/4.86  tff(c_9624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_9609])).
% 11.66/4.86  tff(c_9625, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_9577])).
% 11.66/4.86  tff(c_38, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.66/4.86  tff(c_431, plain, (![A_131, B_132, C_133, D_134]: (k5_mcart_1(A_131, B_132, C_133, D_134)=k1_mcart_1(k1_mcart_1(D_134)) | ~m1_subset_1(D_134, k3_zfmisc_1(A_131, B_132, C_133)) | k1_xboole_0=C_133 | k1_xboole_0=B_132 | k1_xboole_0=A_131)), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.66/4.86  tff(c_470, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_431])).
% 11.66/4.86  tff(c_491, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_470])).
% 11.66/4.86  tff(c_9626, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_9577])).
% 11.66/4.86  tff(c_12, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.66/4.86  tff(c_151, plain, (![A_77, B_78, C_79]: (r2_hidden(k1_mcart_1(A_77), B_78) | ~r2_hidden(A_77, k2_zfmisc_1(B_78, C_79)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.66/4.86  tff(c_9651, plain, (![A_605, B_606, C_607]: (r2_hidden(k1_mcart_1(A_605), B_606) | v1_xboole_0(k2_zfmisc_1(B_606, C_607)) | ~m1_subset_1(A_605, k2_zfmisc_1(B_606, C_607)))), inference(resolution, [status(thm)], [c_6, c_151])).
% 11.66/4.86  tff(c_9706, plain, (![A_605, A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_605), k2_zfmisc_1(A_11, B_12)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)) | ~m1_subset_1(A_605, k3_zfmisc_1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_9651])).
% 11.66/4.86  tff(c_13196, plain, (![A_765, A_766, B_767, C_768]: (r2_hidden(k1_mcart_1(A_765), k2_zfmisc_1(A_766, B_767)) | v1_xboole_0(k3_zfmisc_1(A_766, B_767, C_768)) | ~m1_subset_1(A_765, k3_zfmisc_1(A_766, B_767, C_768)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_9706])).
% 11.66/4.86  tff(c_13314, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_13196])).
% 11.66/4.86  tff(c_13362, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_9626, c_13314])).
% 11.66/4.86  tff(c_20, plain, (![A_22, B_23, C_24]: (r2_hidden(k1_mcart_1(A_22), B_23) | ~r2_hidden(A_22, k2_zfmisc_1(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.66/4.86  tff(c_13369, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_13362, c_20])).
% 11.66/4.86  tff(c_13379, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_491, c_13369])).
% 11.66/4.86  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.66/4.86  tff(c_13402, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_13379, c_4])).
% 11.66/4.86  tff(c_559, plain, (![A_141, B_142, C_143, D_144]: (k6_mcart_1(A_141, B_142, C_143, D_144)=k2_mcart_1(k1_mcart_1(D_144)) | ~m1_subset_1(D_144, k3_zfmisc_1(A_141, B_142, C_143)) | k1_xboole_0=C_143 | k1_xboole_0=B_142 | k1_xboole_0=A_141)), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.66/4.86  tff(c_598, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_559])).
% 11.66/4.86  tff(c_619, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_598])).
% 11.66/4.86  tff(c_18, plain, (![A_22, C_24, B_23]: (r2_hidden(k2_mcart_1(A_22), C_24) | ~r2_hidden(A_22, k2_zfmisc_1(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.66/4.86  tff(c_13371, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_13362, c_18])).
% 11.66/4.86  tff(c_13381, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_619, c_13371])).
% 11.66/4.86  tff(c_13409, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_13381, c_4])).
% 11.66/4.86  tff(c_22, plain, (![A_25, B_26]: (k4_tarski(k1_mcart_1(A_25), k2_mcart_1(A_25))=A_25 | ~r2_hidden(A_25, B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.66/4.86  tff(c_13367, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_13362, c_22])).
% 11.66/4.86  tff(c_13377, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_491, c_619, c_13367])).
% 11.66/4.86  tff(c_10, plain, (![A_8, B_9, C_10]: (k4_tarski(k4_tarski(A_8, B_9), C_10)=k3_mcart_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.66/4.86  tff(c_16286, plain, (![C_878]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_878)=k4_tarski(k1_mcart_1('#skF_5'), C_878))), inference(superposition, [status(thm), theory('equality')], [c_13377, c_10])).
% 11.66/4.86  tff(c_46, plain, (![G_46, F_42, H_48]: (G_46='#skF_4' | k3_mcart_1(F_42, G_46, H_48)!='#skF_5' | ~m1_subset_1(H_48, '#skF_3') | ~m1_subset_1(G_46, '#skF_2') | ~m1_subset_1(F_42, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.66/4.86  tff(c_16293, plain, (![C_878]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_878)!='#skF_5' | ~m1_subset_1(C_878, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16286, c_46])).
% 11.66/4.86  tff(c_16300, plain, (![C_878]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_878)!='#skF_5' | ~m1_subset_1(C_878, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13402, c_13409, c_16293])).
% 11.66/4.86  tff(c_16303, plain, (![C_879]: (k4_tarski(k1_mcart_1('#skF_5'), C_879)!='#skF_5' | ~m1_subset_1(C_879, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_16300])).
% 11.66/4.86  tff(c_16306, plain, (~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9625, c_16303])).
% 11.66/4.86  tff(c_16310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_409, c_16306])).
% 11.66/4.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.66/4.86  
% 11.66/4.86  Inference rules
% 11.66/4.86  ----------------------
% 11.66/4.86  #Ref     : 0
% 11.66/4.86  #Sup     : 4248
% 11.66/4.86  #Fact    : 0
% 11.66/4.86  #Define  : 0
% 11.66/4.86  #Split   : 12
% 11.66/4.86  #Chain   : 0
% 11.66/4.86  #Close   : 0
% 11.66/4.86  
% 11.66/4.86  Ordering : KBO
% 11.66/4.86  
% 11.66/4.86  Simplification rules
% 11.66/4.86  ----------------------
% 11.66/4.86  #Subsume      : 813
% 11.66/4.86  #Demod        : 634
% 11.66/4.86  #Tautology    : 328
% 11.66/4.86  #SimpNegUnit  : 14
% 11.66/4.86  #BackRed      : 4
% 11.66/4.86  
% 11.66/4.86  #Partial instantiations: 0
% 11.66/4.86  #Strategies tried      : 1
% 11.66/4.86  
% 11.66/4.86  Timing (in seconds)
% 11.66/4.86  ----------------------
% 11.66/4.86  Preprocessing        : 0.34
% 11.66/4.87  Parsing              : 0.18
% 11.66/4.87  CNF conversion       : 0.02
% 11.66/4.87  Main loop            : 3.75
% 11.66/4.87  Inferencing          : 0.94
% 11.66/4.87  Reduction            : 0.77
% 11.66/4.87  Demodulation         : 0.51
% 11.66/4.87  BG Simplification    : 0.14
% 11.66/4.87  Subsumption          : 1.63
% 11.66/4.87  Abstraction          : 0.21
% 11.66/4.87  MUC search           : 0.00
% 11.66/4.87  Cooper               : 0.00
% 11.66/4.87  Total                : 4.13
% 11.66/4.87  Index Insertion      : 0.00
% 11.66/4.87  Index Deletion       : 0.00
% 11.66/4.87  Index Matching       : 0.00
% 11.66/4.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
