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
% DateTime   : Thu Dec  3 10:10:05 EST 2020

% Result     : Theorem 10.56s
% Output     : CNFRefutation 10.73s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 307 expanded)
%              Number of leaves         :   35 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 (1007 expanded)
%              Number of equality atoms :   82 ( 546 expanded)
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
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

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

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
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

tff(c_38,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_429,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_38])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22,D_23] :
      ( m1_subset_1(k7_mcart_1(A_20,B_21,C_22,D_23),C_22)
      | ~ m1_subset_1(D_23,k3_zfmisc_1(A_20,B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_433,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_16])).

tff(c_437,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_433])).

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

tff(c_7040,plain,(
    ! [A_552,B_553] :
      ( k4_tarski(k1_mcart_1(A_552),k2_mcart_1(A_552)) = A_552
      | ~ v1_relat_1(B_553)
      | v1_xboole_0(B_553)
      | ~ m1_subset_1(A_552,B_553) ) ),
    inference(resolution,[status(thm)],[c_4,c_143])).

tff(c_7052,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_7040])).

tff(c_7062,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_7052])).

tff(c_7063,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7062])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7067,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7063,c_2])).

tff(c_24,plain,(
    ! [A_29,B_30,C_31] :
      ( k3_zfmisc_1(A_29,B_30,C_31) != k1_xboole_0
      | k1_xboole_0 = C_31
      | k1_xboole_0 = B_30
      | k1_xboole_0 = A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7092,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7067,c_24])).

tff(c_7107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_7092])).

tff(c_7108,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7062])).

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

tff(c_439,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k6_mcart_1(A_131,B_132,C_133,D_134) = k2_mcart_1(k1_mcart_1(D_134))
      | ~ m1_subset_1(D_134,k3_zfmisc_1(A_131,B_132,C_133))
      | k1_xboole_0 = C_133
      | k1_xboole_0 = B_132
      | k1_xboole_0 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_454,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_439])).

tff(c_469,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_454])).

tff(c_554,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k5_mcart_1(A_139,B_140,C_141,D_142) = k1_mcart_1(k1_mcart_1(D_142))
      | ~ m1_subset_1(D_142,k3_zfmisc_1(A_139,B_140,C_141))
      | k1_xboole_0 = C_141
      | k1_xboole_0 = B_140
      | k1_xboole_0 = A_139 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_569,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_554])).

tff(c_584,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_569])).

tff(c_7109,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7062])).

tff(c_20,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden(k1_mcart_1(A_24),B_25)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6176,plain,(
    ! [A_475,A_476,B_477,C_478] :
      ( r2_hidden(k1_mcart_1(A_475),k2_zfmisc_1(A_476,B_477))
      | ~ r2_hidden(A_475,k3_zfmisc_1(A_476,B_477,C_478)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_20])).

tff(c_11068,plain,(
    ! [A_760,A_761,B_762,C_763] :
      ( r2_hidden(k1_mcart_1(A_760),k2_zfmisc_1(A_761,B_762))
      | v1_xboole_0(k3_zfmisc_1(A_761,B_762,C_763))
      | ~ m1_subset_1(A_760,k3_zfmisc_1(A_761,B_762,C_763)) ) ),
    inference(resolution,[status(thm)],[c_4,c_6176])).

tff(c_11081,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_11068])).

tff(c_11094,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_7109,c_11081])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( k4_tarski(k1_mcart_1(A_27),k2_mcart_1(A_27)) = A_27
      | ~ r2_hidden(A_27,B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_11099,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_11094,c_22])).

tff(c_11106,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_469,c_584,c_11099])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_tarski(k4_tarski(A_6,B_7),C_8) = k3_mcart_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11367,plain,(
    ! [C_776] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_776) = k4_tarski(k1_mcart_1('#skF_5'),C_776) ),
    inference(superposition,[status(thm),theory(equality)],[c_11106,c_8])).

tff(c_46,plain,(
    ! [H_50,F_44,G_48] :
      ( H_50 = '#skF_4'
      | k3_mcart_1(F_44,G_48,H_50) != '#skF_5'
      | ~ m1_subset_1(H_50,'#skF_3')
      | ~ m1_subset_1(G_48,'#skF_2')
      | ~ m1_subset_1(F_44,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_11374,plain,(
    ! [C_776] :
      ( C_776 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_776) != '#skF_5'
      | ~ m1_subset_1(C_776,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11367,c_46])).

tff(c_11503,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_11374])).

tff(c_11506,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_11503])).

tff(c_11510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_11506])).

tff(c_11511,plain,(
    ! [C_776] :
      ( ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | C_776 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_776) != '#skF_5'
      | ~ m1_subset_1(C_776,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_11374])).

tff(c_11703,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_11511])).

tff(c_11706,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_11703])).

tff(c_11710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_11706])).

tff(c_11716,plain,(
    ! [C_799] :
      ( C_799 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_799) != '#skF_5'
      | ~ m1_subset_1(C_799,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_11511])).

tff(c_11719,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7108,c_11716])).

tff(c_11722,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_11719])).

tff(c_11724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_429,c_11722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.56/4.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.56/4.25  
% 10.56/4.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.56/4.25  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.56/4.25  
% 10.56/4.25  %Foreground sorts:
% 10.56/4.25  
% 10.56/4.25  
% 10.56/4.25  %Background operators:
% 10.56/4.25  
% 10.56/4.25  
% 10.56/4.25  %Foreground operators:
% 10.56/4.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.56/4.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.56/4.25  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.56/4.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.56/4.25  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 10.56/4.25  tff('#skF_5', type, '#skF_5': $i).
% 10.56/4.25  tff('#skF_2', type, '#skF_2': $i).
% 10.56/4.25  tff('#skF_3', type, '#skF_3': $i).
% 10.56/4.25  tff('#skF_1', type, '#skF_1': $i).
% 10.56/4.25  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 10.56/4.25  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 10.56/4.25  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 10.56/4.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.56/4.25  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 10.56/4.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.56/4.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.56/4.25  tff('#skF_4', type, '#skF_4': $i).
% 10.56/4.25  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 10.56/4.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.56/4.25  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 10.56/4.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.56/4.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.56/4.25  
% 10.73/4.27  tff(f_121, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 10.73/4.27  tff(f_97, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 10.73/4.27  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 10.73/4.27  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 10.73/4.27  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.73/4.27  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 10.73/4.27  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 10.73/4.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.73/4.27  tff(f_77, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 10.73/4.27  tff(f_49, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 10.73/4.27  tff(f_45, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 10.73/4.27  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 10.73/4.27  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 10.73/4.27  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.73/4.27  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.73/4.27  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.73/4.27  tff(c_48, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.73/4.27  tff(c_395, plain, (![A_127, B_128, C_129, D_130]: (k7_mcart_1(A_127, B_128, C_129, D_130)=k2_mcart_1(D_130) | ~m1_subset_1(D_130, k3_zfmisc_1(A_127, B_128, C_129)) | k1_xboole_0=C_129 | k1_xboole_0=B_128 | k1_xboole_0=A_127)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.73/4.27  tff(c_410, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_395])).
% 10.73/4.27  tff(c_425, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_410])).
% 10.73/4.27  tff(c_38, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.73/4.27  tff(c_429, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_425, c_38])).
% 10.73/4.27  tff(c_16, plain, (![A_20, B_21, C_22, D_23]: (m1_subset_1(k7_mcart_1(A_20, B_21, C_22, D_23), C_22) | ~m1_subset_1(D_23, k3_zfmisc_1(A_20, B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.73/4.27  tff(c_433, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_16])).
% 10.73/4.27  tff(c_437, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_433])).
% 10.73/4.27  tff(c_122, plain, (![A_71, B_72, C_73]: (k2_zfmisc_1(k2_zfmisc_1(A_71, B_72), C_73)=k3_zfmisc_1(A_71, B_72, C_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.73/4.27  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.73/4.27  tff(c_134, plain, (![A_71, B_72, C_73]: (v1_relat_1(k3_zfmisc_1(A_71, B_72, C_73)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_6])).
% 10.73/4.27  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.73/4.27  tff(c_143, plain, (![A_74, B_75]: (k4_tarski(k1_mcart_1(A_74), k2_mcart_1(A_74))=A_74 | ~r2_hidden(A_74, B_75) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.73/4.27  tff(c_7040, plain, (![A_552, B_553]: (k4_tarski(k1_mcart_1(A_552), k2_mcart_1(A_552))=A_552 | ~v1_relat_1(B_553) | v1_xboole_0(B_553) | ~m1_subset_1(A_552, B_553))), inference(resolution, [status(thm)], [c_4, c_143])).
% 10.73/4.27  tff(c_7052, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_7040])).
% 10.73/4.27  tff(c_7062, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_7052])).
% 10.73/4.27  tff(c_7063, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_7062])).
% 10.73/4.27  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.73/4.27  tff(c_7067, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_7063, c_2])).
% 10.73/4.27  tff(c_24, plain, (![A_29, B_30, C_31]: (k3_zfmisc_1(A_29, B_30, C_31)!=k1_xboole_0 | k1_xboole_0=C_31 | k1_xboole_0=B_30 | k1_xboole_0=A_29)), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.73/4.27  tff(c_7092, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7067, c_24])).
% 10.73/4.27  tff(c_7107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_7092])).
% 10.73/4.27  tff(c_7108, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_7062])).
% 10.73/4.27  tff(c_14, plain, (![A_16, B_17, C_18, D_19]: (m1_subset_1(k6_mcart_1(A_16, B_17, C_18, D_19), B_17) | ~m1_subset_1(D_19, k3_zfmisc_1(A_16, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.73/4.27  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (m1_subset_1(k5_mcart_1(A_12, B_13, C_14, D_15), A_12) | ~m1_subset_1(D_15, k3_zfmisc_1(A_12, B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.73/4.27  tff(c_439, plain, (![A_131, B_132, C_133, D_134]: (k6_mcart_1(A_131, B_132, C_133, D_134)=k2_mcart_1(k1_mcart_1(D_134)) | ~m1_subset_1(D_134, k3_zfmisc_1(A_131, B_132, C_133)) | k1_xboole_0=C_133 | k1_xboole_0=B_132 | k1_xboole_0=A_131)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.73/4.27  tff(c_454, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_439])).
% 10.73/4.27  tff(c_469, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_454])).
% 10.73/4.27  tff(c_554, plain, (![A_139, B_140, C_141, D_142]: (k5_mcart_1(A_139, B_140, C_141, D_142)=k1_mcart_1(k1_mcart_1(D_142)) | ~m1_subset_1(D_142, k3_zfmisc_1(A_139, B_140, C_141)) | k1_xboole_0=C_141 | k1_xboole_0=B_140 | k1_xboole_0=A_139)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.73/4.27  tff(c_569, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_554])).
% 10.73/4.27  tff(c_584, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_569])).
% 10.73/4.27  tff(c_7109, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_7062])).
% 10.73/4.27  tff(c_20, plain, (![A_24, B_25, C_26]: (r2_hidden(k1_mcart_1(A_24), B_25) | ~r2_hidden(A_24, k2_zfmisc_1(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.73/4.27  tff(c_6176, plain, (![A_475, A_476, B_477, C_478]: (r2_hidden(k1_mcart_1(A_475), k2_zfmisc_1(A_476, B_477)) | ~r2_hidden(A_475, k3_zfmisc_1(A_476, B_477, C_478)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_20])).
% 10.73/4.27  tff(c_11068, plain, (![A_760, A_761, B_762, C_763]: (r2_hidden(k1_mcart_1(A_760), k2_zfmisc_1(A_761, B_762)) | v1_xboole_0(k3_zfmisc_1(A_761, B_762, C_763)) | ~m1_subset_1(A_760, k3_zfmisc_1(A_761, B_762, C_763)))), inference(resolution, [status(thm)], [c_4, c_6176])).
% 10.73/4.27  tff(c_11081, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_11068])).
% 10.73/4.27  tff(c_11094, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_7109, c_11081])).
% 10.73/4.27  tff(c_22, plain, (![A_27, B_28]: (k4_tarski(k1_mcart_1(A_27), k2_mcart_1(A_27))=A_27 | ~r2_hidden(A_27, B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.73/4.27  tff(c_11099, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_11094, c_22])).
% 10.73/4.27  tff(c_11106, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_469, c_584, c_11099])).
% 10.73/4.27  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_tarski(k4_tarski(A_6, B_7), C_8)=k3_mcart_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.73/4.27  tff(c_11367, plain, (![C_776]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_776)=k4_tarski(k1_mcart_1('#skF_5'), C_776))), inference(superposition, [status(thm), theory('equality')], [c_11106, c_8])).
% 10.73/4.27  tff(c_46, plain, (![H_50, F_44, G_48]: (H_50='#skF_4' | k3_mcart_1(F_44, G_48, H_50)!='#skF_5' | ~m1_subset_1(H_50, '#skF_3') | ~m1_subset_1(G_48, '#skF_2') | ~m1_subset_1(F_44, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 10.73/4.27  tff(c_11374, plain, (![C_776]: (C_776='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_776)!='#skF_5' | ~m1_subset_1(C_776, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_11367, c_46])).
% 10.73/4.27  tff(c_11503, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_11374])).
% 10.73/4.27  tff(c_11506, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_11503])).
% 10.73/4.27  tff(c_11510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_11506])).
% 10.73/4.27  tff(c_11511, plain, (![C_776]: (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | C_776='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_776)!='#skF_5' | ~m1_subset_1(C_776, '#skF_3'))), inference(splitRight, [status(thm)], [c_11374])).
% 10.73/4.27  tff(c_11703, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_11511])).
% 10.73/4.27  tff(c_11706, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_14, c_11703])).
% 10.73/4.27  tff(c_11710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_11706])).
% 10.73/4.27  tff(c_11716, plain, (![C_799]: (C_799='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_799)!='#skF_5' | ~m1_subset_1(C_799, '#skF_3'))), inference(splitRight, [status(thm)], [c_11511])).
% 10.73/4.27  tff(c_11719, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7108, c_11716])).
% 10.73/4.27  tff(c_11722, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_437, c_11719])).
% 10.73/4.27  tff(c_11724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_429, c_11722])).
% 10.73/4.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.73/4.27  
% 10.73/4.27  Inference rules
% 10.73/4.27  ----------------------
% 10.73/4.27  #Ref     : 0
% 10.73/4.27  #Sup     : 3287
% 10.73/4.27  #Fact    : 0
% 10.73/4.27  #Define  : 0
% 10.73/4.27  #Split   : 17
% 10.73/4.27  #Chain   : 0
% 10.73/4.27  #Close   : 0
% 10.73/4.27  
% 10.73/4.27  Ordering : KBO
% 10.73/4.27  
% 10.73/4.27  Simplification rules
% 10.73/4.27  ----------------------
% 10.73/4.27  #Subsume      : 585
% 10.73/4.27  #Demod        : 636
% 10.73/4.27  #Tautology    : 322
% 10.73/4.27  #SimpNegUnit  : 14
% 10.73/4.27  #BackRed      : 5
% 10.73/4.27  
% 10.73/4.27  #Partial instantiations: 0
% 10.73/4.27  #Strategies tried      : 1
% 10.73/4.27  
% 10.73/4.27  Timing (in seconds)
% 10.73/4.27  ----------------------
% 10.77/4.27  Preprocessing        : 0.36
% 10.77/4.27  Parsing              : 0.19
% 10.77/4.27  CNF conversion       : 0.03
% 10.77/4.27  Main loop            : 3.10
% 10.77/4.27  Inferencing          : 0.78
% 10.77/4.27  Reduction            : 0.64
% 10.77/4.27  Demodulation         : 0.44
% 10.77/4.28  BG Simplification    : 0.11
% 10.77/4.28  Subsumption          : 1.38
% 10.77/4.28  Abstraction          : 0.13
% 10.77/4.28  MUC search           : 0.00
% 10.77/4.28  Cooper               : 0.00
% 10.77/4.28  Total                : 3.49
% 10.77/4.28  Index Insertion      : 0.00
% 10.77/4.28  Index Deletion       : 0.00
% 10.77/4.28  Index Matching       : 0.00
% 10.77/4.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
