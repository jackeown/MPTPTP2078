%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0903+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:02 EST 2020

% Result     : Theorem 8.76s
% Output     : CNFRefutation 9.14s
% Verified   : 
% Statistics : Number of formulae       :  155 (1537 expanded)
%              Number of leaves         :   39 ( 465 expanded)
%              Depth                    :   14
%              Number of atoms          :  282 (4950 expanded)
%              Number of equality atoms :  135 (1486 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ ( ~ r1_tarski(A,k4_zfmisc_1(A,B,C,D))
            & ~ r1_tarski(A,k4_zfmisc_1(B,C,D,A))
            & ~ r1_tarski(A,k4_zfmisc_1(C,D,A,B))
            & ~ r1_tarski(A,k4_zfmisc_1(D,A,B,C)) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_mcart_1)).

tff(f_64,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_130,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_mcart_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_72,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
          & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
          & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_18,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_1'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4148,plain,(
    ! [A_585,B_586] :
      ( m1_subset_1(A_585,B_586)
      | ~ r2_hidden(A_585,B_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4152,plain,(
    ! [A_22] :
      ( m1_subset_1('#skF_1'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(resolution,[status(thm)],[c_18,c_4148])).

tff(c_154,plain,(
    ! [A_83,B_84] :
      ( m1_subset_1(A_83,B_84)
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_158,plain,(
    ! [A_22] :
      ( m1_subset_1('#skF_1'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(resolution,[status(thm)],[c_18,c_154])).

tff(c_58,plain,
    ( r1_tarski('#skF_2',k4_zfmisc_1('#skF_5','#skF_2','#skF_3','#skF_4'))
    | r1_tarski('#skF_2',k4_zfmisc_1('#skF_4','#skF_5','#skF_2','#skF_3'))
    | r1_tarski('#skF_2',k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_2'))
    | r1_tarski('#skF_2',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_99,plain,(
    r1_tarski('#skF_2',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_242,plain,(
    ! [A_108,C_109,B_110] :
      ( m1_subset_1(A_108,C_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(C_109))
      | ~ r2_hidden(A_108,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_270,plain,(
    ! [A_115,B_116,A_117] :
      ( m1_subset_1(A_115,B_116)
      | ~ r2_hidden(A_115,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(resolution,[status(thm)],[c_26,c_242])).

tff(c_377,plain,(
    ! [A_136,B_137,B_138] :
      ( m1_subset_1(A_136,B_137)
      | ~ r1_tarski(B_138,B_137)
      | v1_xboole_0(B_138)
      | ~ m1_subset_1(A_136,B_138) ) ),
    inference(resolution,[status(thm)],[c_16,c_270])).

tff(c_389,plain,(
    ! [A_136] :
      ( m1_subset_1(A_136,k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_136,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_99,c_377])).

tff(c_405,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_52,plain,(
    ! [A_63] :
      ( k1_xboole_0 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_408,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_405,c_52])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_408])).

tff(c_414,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_413,plain,(
    ! [A_136] :
      ( m1_subset_1(A_136,k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(A_136,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_8,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] :
      ( m1_subset_1(k8_mcart_1(A_8,B_9,C_10,D_11,E_12),A_8)
      | ~ m1_subset_1(E_12,k4_zfmisc_1(A_8,B_9,C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_682,plain,(
    ! [D_223,B_220,C_224,E_221,A_222] :
      ( k4_mcart_1(k8_mcart_1(A_222,B_220,C_224,D_223,E_221),k9_mcart_1(A_222,B_220,C_224,D_223,E_221),k10_mcart_1(A_222,B_220,C_224,D_223,E_221),k11_mcart_1(A_222,B_220,C_224,D_223,E_221)) = E_221
      | ~ m1_subset_1(E_221,k4_zfmisc_1(A_222,B_220,C_224,D_223))
      | k1_xboole_0 = D_223
      | k1_xboole_0 = C_224
      | k1_xboole_0 = B_220
      | k1_xboole_0 = A_222 ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_434,plain,(
    ! [F_155,E_156,A_153,D_154,C_157] :
      ( ~ r2_hidden(C_157,A_153)
      | k4_mcart_1(C_157,D_154,E_156,F_155) != '#skF_1'(A_153)
      | k1_xboole_0 = A_153 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_439,plain,(
    ! [A_20,B_21,F_155,E_156,D_154] :
      ( k4_mcart_1(A_20,D_154,E_156,F_155) != '#skF_1'(B_21)
      | k1_xboole_0 = B_21
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_16,c_434])).

tff(c_2802,plain,(
    ! [C_502,A_506,B_504,B_503,E_505,D_501] :
      ( E_505 != '#skF_1'(B_503)
      | k1_xboole_0 = B_503
      | v1_xboole_0(B_503)
      | ~ m1_subset_1(k8_mcart_1(A_506,B_504,C_502,D_501,E_505),B_503)
      | ~ m1_subset_1(E_505,k4_zfmisc_1(A_506,B_504,C_502,D_501))
      | k1_xboole_0 = D_501
      | k1_xboole_0 = C_502
      | k1_xboole_0 = B_504
      | k1_xboole_0 = A_506 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_682,c_439])).

tff(c_2967,plain,(
    ! [C_536,A_533,D_537,B_535,E_534] :
      ( E_534 != '#skF_1'(A_533)
      | v1_xboole_0(A_533)
      | k1_xboole_0 = D_537
      | k1_xboole_0 = C_536
      | k1_xboole_0 = B_535
      | k1_xboole_0 = A_533
      | ~ m1_subset_1(E_534,k4_zfmisc_1(A_533,B_535,C_536,D_537)) ) ),
    inference(resolution,[status(thm)],[c_8,c_2802])).

tff(c_3002,plain,(
    ! [A_136] :
      ( A_136 != '#skF_1'('#skF_2')
      | v1_xboole_0('#skF_2')
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(A_136,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_413,c_2967])).

tff(c_3033,plain,(
    ! [A_136] :
      ( A_136 != '#skF_1'('#skF_2')
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(A_136,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_414,c_3002])).

tff(c_3096,plain,(
    ! [A_539] :
      ( A_539 != '#skF_1'('#skF_2')
      | ~ m1_subset_1(A_539,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_3033])).

tff(c_3136,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_158,c_3096])).

tff(c_3149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3136])).

tff(c_3150,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3033])).

tff(c_3151,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3150])).

tff(c_3258,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_56])).

tff(c_42,plain,(
    ! [A_53,B_54,C_55] : k4_zfmisc_1(A_53,B_54,C_55,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3249,plain,(
    ! [A_53,B_54,C_55] : k4_zfmisc_1(A_53,B_54,C_55,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_3151,c_42])).

tff(c_3485,plain,(
    r1_tarski('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3249,c_99])).

tff(c_28,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3254,plain,(
    ! [A_42] :
      ( A_42 = '#skF_5'
      | ~ r1_tarski(A_42,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_3151,c_28])).

tff(c_3533,plain,(
    '#skF_5' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3485,c_3254])).

tff(c_3539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3258,c_3533])).

tff(c_3540,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3150])).

tff(c_3542,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3540])).

tff(c_3650,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3542,c_56])).

tff(c_46,plain,(
    ! [A_53,C_55,D_56] : k4_zfmisc_1(A_53,k1_xboole_0,C_55,D_56) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3643,plain,(
    ! [A_53,C_55,D_56] : k4_zfmisc_1(A_53,'#skF_3',C_55,D_56) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3542,c_3542,c_46])).

tff(c_3825,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3643,c_99])).

tff(c_3646,plain,(
    ! [A_42] :
      ( A_42 = '#skF_3'
      | ~ r1_tarski(A_42,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3542,c_3542,c_28])).

tff(c_3858,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3825,c_3646])).

tff(c_3864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3650,c_3858])).

tff(c_3865,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3540])).

tff(c_3974,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3865,c_56])).

tff(c_44,plain,(
    ! [A_53,B_54,D_56] : k4_zfmisc_1(A_53,B_54,k1_xboole_0,D_56) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3969,plain,(
    ! [A_53,B_54,D_56] : k4_zfmisc_1(A_53,B_54,'#skF_4',D_56) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3865,c_3865,c_44])).

tff(c_4061,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3969,c_99])).

tff(c_3970,plain,(
    ! [A_42] :
      ( A_42 = '#skF_4'
      | ~ r1_tarski(A_42,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3865,c_3865,c_28])).

tff(c_4085,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4061,c_3970])).

tff(c_4091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3974,c_4085])).

tff(c_4092,plain,
    ( r1_tarski('#skF_2',k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_2'))
    | r1_tarski('#skF_2',k4_zfmisc_1('#skF_4','#skF_5','#skF_2','#skF_3'))
    | r1_tarski('#skF_2',k4_zfmisc_1('#skF_5','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4165,plain,(
    r1_tarski('#skF_2',k4_zfmisc_1('#skF_5','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4092])).

tff(c_4214,plain,(
    ! [A_607,C_608,B_609] :
      ( m1_subset_1(A_607,C_608)
      | ~ m1_subset_1(B_609,k1_zfmisc_1(C_608))
      | ~ r2_hidden(A_607,B_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4247,plain,(
    ! [A_613,B_614,A_615] :
      ( m1_subset_1(A_613,B_614)
      | ~ r2_hidden(A_613,A_615)
      | ~ r1_tarski(A_615,B_614) ) ),
    inference(resolution,[status(thm)],[c_26,c_4214])).

tff(c_4380,plain,(
    ! [A_647,B_648,B_649] :
      ( m1_subset_1(A_647,B_648)
      | ~ r1_tarski(B_649,B_648)
      | v1_xboole_0(B_649)
      | ~ m1_subset_1(A_647,B_649) ) ),
    inference(resolution,[status(thm)],[c_16,c_4247])).

tff(c_4392,plain,(
    ! [A_647] :
      ( m1_subset_1(A_647,k4_zfmisc_1('#skF_5','#skF_2','#skF_3','#skF_4'))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_647,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4165,c_4380])).

tff(c_4426,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4392])).

tff(c_4429,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4426,c_52])).

tff(c_4433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4429])).

tff(c_4435,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4392])).

tff(c_4434,plain,(
    ! [A_647] :
      ( m1_subset_1(A_647,k4_zfmisc_1('#skF_5','#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(A_647,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_4392])).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] :
      ( m1_subset_1(k9_mcart_1(A_13,B_14,C_15,D_16,E_17),B_14)
      | ~ m1_subset_1(E_17,k4_zfmisc_1(A_13,B_14,C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4677,plain,(
    ! [E_723,C_726,B_722,A_724,D_725] :
      ( k4_mcart_1(k8_mcart_1(A_724,B_722,C_726,D_725,E_723),k9_mcart_1(A_724,B_722,C_726,D_725,E_723),k10_mcart_1(A_724,B_722,C_726,D_725,E_723),k11_mcart_1(A_724,B_722,C_726,D_725,E_723)) = E_723
      | ~ m1_subset_1(E_723,k4_zfmisc_1(A_724,B_722,C_726,D_725))
      | k1_xboole_0 = D_725
      | k1_xboole_0 = C_726
      | k1_xboole_0 = B_722
      | k1_xboole_0 = A_724 ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4336,plain,(
    ! [C_634,A_630,F_632,E_633,D_631] :
      ( ~ r2_hidden(D_631,A_630)
      | k4_mcart_1(C_634,D_631,E_633,F_632) != '#skF_1'(A_630)
      | k1_xboole_0 = A_630 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4341,plain,(
    ! [C_634,A_20,B_21,F_632,E_633] :
      ( k4_mcart_1(C_634,A_20,E_633,F_632) != '#skF_1'(B_21)
      | k1_xboole_0 = B_21
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_16,c_4336])).

tff(c_8925,plain,(
    ! [C_1178,B_1177,B_1176,D_1175,E_1174,A_1173] :
      ( E_1174 != '#skF_1'(B_1177)
      | k1_xboole_0 = B_1177
      | v1_xboole_0(B_1177)
      | ~ m1_subset_1(k9_mcart_1(A_1173,B_1176,C_1178,D_1175,E_1174),B_1177)
      | ~ m1_subset_1(E_1174,k4_zfmisc_1(A_1173,B_1176,C_1178,D_1175))
      | k1_xboole_0 = D_1175
      | k1_xboole_0 = C_1178
      | k1_xboole_0 = B_1176
      | k1_xboole_0 = A_1173 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4677,c_4341])).

tff(c_8963,plain,(
    ! [B_1180,D_1179,A_1182,E_1181,C_1183] :
      ( E_1181 != '#skF_1'(B_1180)
      | v1_xboole_0(B_1180)
      | k1_xboole_0 = D_1179
      | k1_xboole_0 = C_1183
      | k1_xboole_0 = B_1180
      | k1_xboole_0 = A_1182
      | ~ m1_subset_1(E_1181,k4_zfmisc_1(A_1182,B_1180,C_1183,D_1179)) ) ),
    inference(resolution,[status(thm)],[c_10,c_8925])).

tff(c_8998,plain,(
    ! [A_647] :
      ( A_647 != '#skF_1'('#skF_2')
      | v1_xboole_0('#skF_2')
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(A_647,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4434,c_8963])).

tff(c_9029,plain,(
    ! [A_647] :
      ( A_647 != '#skF_1'('#skF_2')
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(A_647,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4435,c_8998])).

tff(c_9039,plain,(
    ! [A_1184] :
      ( A_1184 != '#skF_1'('#skF_2')
      | ~ m1_subset_1(A_1184,'#skF_2') ) ),
    inference(splitLeft,[status(thm)],[c_9029])).

tff(c_9079,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4152,c_9039])).

tff(c_9092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9079])).

tff(c_9093,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9029])).

tff(c_9094,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9093])).

tff(c_9188,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9094,c_56])).

tff(c_9179,plain,(
    ! [A_53,B_54,C_55] : k4_zfmisc_1(A_53,B_54,C_55,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9094,c_9094,c_42])).

tff(c_9329,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9179,c_4165])).

tff(c_9184,plain,(
    ! [A_42] :
      ( A_42 = '#skF_4'
      | ~ r1_tarski(A_42,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9094,c_9094,c_28])).

tff(c_9353,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9329,c_9184])).

tff(c_9359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9188,c_9353])).

tff(c_9360,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9093])).

tff(c_9362,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9360])).

tff(c_9448,plain,(
    ! [A_53,B_54,C_55] : k4_zfmisc_1(A_53,B_54,C_55,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9362,c_9362,c_42])).

tff(c_4093,plain,(
    ~ r1_tarski('#skF_2',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_9644,plain,(
    ~ r1_tarski('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9448,c_4093])).

tff(c_48,plain,(
    ! [B_54,C_55,D_56] : k4_zfmisc_1(k1_xboole_0,B_54,C_55,D_56) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_9449,plain,(
    ! [B_54,C_55,D_56] : k4_zfmisc_1('#skF_5',B_54,C_55,D_56) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9362,c_9362,c_48])).

tff(c_9676,plain,(
    r1_tarski('#skF_2','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9449,c_4165])).

tff(c_9679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9644,c_9676])).

tff(c_9680,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9360])).

tff(c_9769,plain,(
    ! [A_53,C_55,D_56] : k4_zfmisc_1(A_53,'#skF_3',C_55,D_56) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9680,c_9680,c_46])).

tff(c_9883,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9769,c_4093])).

tff(c_9771,plain,(
    ! [A_53,B_54,D_56] : k4_zfmisc_1(A_53,B_54,'#skF_3',D_56) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9680,c_9680,c_44])).

tff(c_9944,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9771,c_4165])).

tff(c_9947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9883,c_9944])).

tff(c_9948,plain,
    ( r1_tarski('#skF_2',k4_zfmisc_1('#skF_4','#skF_5','#skF_2','#skF_3'))
    | r1_tarski('#skF_2',k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4092])).

tff(c_9968,plain,(
    r1_tarski('#skF_2',k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9948])).

tff(c_10039,plain,(
    ! [A_1261,B_1262,C_1263,D_1264] : k3_zfmisc_1(k2_zfmisc_1(A_1261,B_1262),C_1263,D_1264) = k4_zfmisc_1(A_1261,B_1262,C_1263,D_1264) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_tarski(A_43,k3_zfmisc_1(B_44,C_45,A_43))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10070,plain,(
    ! [D_1269,A_1270,B_1271,C_1272] :
      ( ~ r1_tarski(D_1269,k4_zfmisc_1(A_1270,B_1271,C_1272,D_1269))
      | k1_xboole_0 = D_1269 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10039,c_32])).

tff(c_10073,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_9968,c_10070])).

tff(c_10089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10073])).

tff(c_10090,plain,(
    r1_tarski('#skF_2',k4_zfmisc_1('#skF_4','#skF_5','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9948])).

tff(c_10226,plain,(
    ! [A_1295,B_1296,C_1297,D_1298] : k3_zfmisc_1(k2_zfmisc_1(A_1295,B_1296),C_1297,D_1298) = k4_zfmisc_1(A_1295,B_1296,C_1297,D_1298) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ! [A_43,C_45,B_44] :
      ( ~ r1_tarski(A_43,k3_zfmisc_1(C_45,A_43,B_44))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10244,plain,(
    ! [C_1299,A_1300,B_1301,D_1302] :
      ( ~ r1_tarski(C_1299,k4_zfmisc_1(A_1300,B_1301,C_1299,D_1302))
      | k1_xboole_0 = C_1299 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10226,c_30])).

tff(c_10251,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10090,c_10244])).

tff(c_10268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_10251])).

%------------------------------------------------------------------------------
