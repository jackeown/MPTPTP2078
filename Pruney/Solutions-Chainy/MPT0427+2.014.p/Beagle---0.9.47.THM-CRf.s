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
% DateTime   : Thu Dec  3 09:57:58 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 374 expanded)
%              Number of leaves         :   34 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 745 expanded)
%              Number of equality atoms :   66 ( 185 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_281,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_300,plain,(
    ! [A_65] : r1_tarski(A_65,A_65) ),
    inference(resolution,[status(thm)],[c_281,c_6])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_412,plain,(
    ! [A_84,C_85,B_86] :
      ( m1_subset_1(A_84,C_85)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(C_85))
      | ~ r2_hidden(A_84,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_440,plain,(
    ! [A_89] :
      ( m1_subset_1(A_89,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_89,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_412])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_448,plain,(
    ! [A_90] :
      ( r1_tarski(A_90,'#skF_5')
      | ~ r2_hidden(A_90,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_440,c_46])).

tff(c_463,plain,
    ( r1_tarski('#skF_4'('#skF_6'),'#skF_5')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28,c_448])).

tff(c_464,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_36,plain,(
    ! [A_21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_38,plain,(
    ! [A_22] :
      ( k8_setfam_1(A_22,k1_xboole_0) = A_22
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_62,plain,(
    ! [A_22] : k8_setfam_1(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_480,plain,(
    ! [A_22] : k8_setfam_1(A_22,'#skF_6') = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_62])).

tff(c_476,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | A_14 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_28])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_752,plain,(
    ! [A_112] :
      ( m1_subset_1(A_112,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_112,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_412])).

tff(c_760,plain,(
    ! [A_113] :
      ( r1_tarski(A_113,'#skF_5')
      | ~ r2_hidden(A_113,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_752,c_46])).

tff(c_769,plain,
    ( r1_tarski('#skF_4'('#skF_7'),'#skF_5')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_476,c_760])).

tff(c_799,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_769])).

tff(c_54,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_5','#skF_7'),k8_setfam_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_503,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_5','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_54])).

tff(c_802,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_503])).

tff(c_808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_480,c_802])).

tff(c_810,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_769])).

tff(c_486,plain,(
    ! [A_91,B_92] :
      ( k6_setfam_1(A_91,B_92) = k1_setfam_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_499,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_486])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k8_setfam_1(A_22,B_23) = k6_setfam_1(A_22,B_23)
      | k1_xboole_0 = B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_812,plain,(
    ! [A_118,B_119] :
      ( k8_setfam_1(A_118,B_119) = k6_setfam_1(A_118,B_119)
      | B_119 = '#skF_6'
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(A_118))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_40])).

tff(c_831,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_58,c_812])).

tff(c_839,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_831])).

tff(c_840,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_810,c_839])).

tff(c_841,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_503])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k8_setfam_1(A_24,B_25),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_845,plain,
    ( m1_subset_1(k1_setfam_1('#skF_7'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_840,c_42])).

tff(c_849,plain,(
    m1_subset_1(k1_setfam_1('#skF_7'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_845])).

tff(c_855,plain,(
    r1_tarski(k1_setfam_1('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_849,c_46])).

tff(c_860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_841,c_855])).

tff(c_862,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_56,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    ! [B_34,A_33] :
      ( r1_tarski(k1_setfam_1(B_34),k1_setfam_1(A_33))
      | k1_xboole_0 = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_863,plain,(
    ! [A_120] :
      ( m1_subset_1(A_120,k1_zfmisc_1('#skF_5'))
      | ~ r2_hidden(A_120,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_58,c_412])).

tff(c_905,plain,(
    ! [A_124] :
      ( r1_tarski(A_124,'#skF_5')
      | ~ r2_hidden(A_124,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_863,c_46])).

tff(c_920,plain,
    ( r1_tarski('#skF_4'('#skF_7'),'#skF_5')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_905])).

tff(c_921,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_920])).

tff(c_923,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_862])).

tff(c_302,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_372,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_4'(A_79),B_80)
      | ~ r1_tarski(A_79,B_80)
      | k1_xboole_0 = A_79 ) ),
    inference(resolution,[status(thm)],[c_28,c_302])).

tff(c_82,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    ! [A_40] : k2_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_32])).

tff(c_224,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_237,plain,(
    ! [B_58] : k4_xboole_0(B_58,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_98])).

tff(c_249,plain,(
    ! [B_59] : k4_xboole_0(B_59,k1_xboole_0) = B_59 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_237])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_258,plain,(
    ! [D_13,B_59] :
      ( ~ r2_hidden(D_13,k1_xboole_0)
      | ~ r2_hidden(D_13,B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_12])).

tff(c_390,plain,(
    ! [A_81,B_82] :
      ( ~ r2_hidden('#skF_4'(A_81),B_82)
      | ~ r1_tarski(A_81,k1_xboole_0)
      | k1_xboole_0 = A_81 ) ),
    inference(resolution,[status(thm)],[c_372,c_258])).

tff(c_398,plain,(
    ! [A_14] :
      ( ~ r1_tarski(A_14,k1_xboole_0)
      | k1_xboole_0 = A_14 ) ),
    inference(resolution,[status(thm)],[c_28,c_390])).

tff(c_1133,plain,(
    ! [A_140] :
      ( ~ r1_tarski(A_140,'#skF_7')
      | A_140 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_921,c_398])).

tff(c_1144,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_56,c_1133])).

tff(c_1152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_923,c_1144])).

tff(c_1154,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_871,plain,(
    ! [A_121,B_122] :
      ( k6_setfam_1(A_121,B_122) = k1_setfam_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k1_zfmisc_1(A_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_888,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_871])).

tff(c_1396,plain,(
    ! [A_170,B_171] :
      ( k8_setfam_1(A_170,B_171) = k6_setfam_1(A_170,B_171)
      | k1_xboole_0 = B_171
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k1_zfmisc_1(A_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1429,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_58,c_1396])).

tff(c_1446,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_1429])).

tff(c_1447,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1154,c_1446])).

tff(c_887,plain,(
    k6_setfam_1('#skF_5','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_871])).

tff(c_1426,plain,
    ( k8_setfam_1('#skF_5','#skF_6') = k6_setfam_1('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_1396])).

tff(c_1443,plain,
    ( k8_setfam_1('#skF_5','#skF_6') = k1_setfam_1('#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_1426])).

tff(c_1444,plain,(
    k8_setfam_1('#skF_5','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_862,c_1443])).

tff(c_1452,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_5','#skF_7'),k1_setfam_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1444,c_54])).

tff(c_1471,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_7'),k1_setfam_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_1452])).

tff(c_1474,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_1471])).

tff(c_1477,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1474])).

tff(c_1479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_862,c_1477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:00:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.48  
% 3.29/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1
% 3.29/1.48  
% 3.29/1.48  %Foreground sorts:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Background operators:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Foreground operators:
% 3.29/1.48  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.48  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.29/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.29/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.29/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.29/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.29/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.48  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.29/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.29/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.29/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.29/1.48  
% 3.43/1.50  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.43/1.50  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.43/1.50  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.43/1.50  tff(f_91, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.43/1.50  tff(f_85, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.43/1.50  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.43/1.50  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.43/1.50  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.43/1.50  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.43/1.50  tff(f_97, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.43/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.43/1.50  tff(f_58, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.43/1.50  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.43/1.50  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.43/1.50  tff(c_281, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.43/1.50  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.43/1.50  tff(c_300, plain, (![A_65]: (r1_tarski(A_65, A_65))), inference(resolution, [status(thm)], [c_281, c_6])).
% 3.43/1.50  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.43/1.50  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.43/1.50  tff(c_412, plain, (![A_84, C_85, B_86]: (m1_subset_1(A_84, C_85) | ~m1_subset_1(B_86, k1_zfmisc_1(C_85)) | ~r2_hidden(A_84, B_86))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.43/1.50  tff(c_440, plain, (![A_89]: (m1_subset_1(A_89, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_89, '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_412])).
% 3.43/1.50  tff(c_46, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.43/1.50  tff(c_448, plain, (![A_90]: (r1_tarski(A_90, '#skF_5') | ~r2_hidden(A_90, '#skF_6'))), inference(resolution, [status(thm)], [c_440, c_46])).
% 3.43/1.50  tff(c_463, plain, (r1_tarski('#skF_4'('#skF_6'), '#skF_5') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_28, c_448])).
% 3.43/1.50  tff(c_464, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_463])).
% 3.43/1.50  tff(c_36, plain, (![A_21]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.43/1.50  tff(c_38, plain, (![A_22]: (k8_setfam_1(A_22, k1_xboole_0)=A_22 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.43/1.50  tff(c_62, plain, (![A_22]: (k8_setfam_1(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 3.43/1.50  tff(c_480, plain, (![A_22]: (k8_setfam_1(A_22, '#skF_6')=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_464, c_62])).
% 3.43/1.50  tff(c_476, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | A_14='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_464, c_28])).
% 3.43/1.50  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.43/1.50  tff(c_752, plain, (![A_112]: (m1_subset_1(A_112, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_112, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_412])).
% 3.43/1.50  tff(c_760, plain, (![A_113]: (r1_tarski(A_113, '#skF_5') | ~r2_hidden(A_113, '#skF_7'))), inference(resolution, [status(thm)], [c_752, c_46])).
% 3.43/1.50  tff(c_769, plain, (r1_tarski('#skF_4'('#skF_7'), '#skF_5') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_476, c_760])).
% 3.43/1.50  tff(c_799, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_769])).
% 3.43/1.50  tff(c_54, plain, (~r1_tarski(k8_setfam_1('#skF_5', '#skF_7'), k8_setfam_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.43/1.50  tff(c_503, plain, (~r1_tarski(k8_setfam_1('#skF_5', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_480, c_54])).
% 3.43/1.50  tff(c_802, plain, (~r1_tarski(k8_setfam_1('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_503])).
% 3.43/1.50  tff(c_808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_480, c_802])).
% 3.43/1.50  tff(c_810, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_769])).
% 3.43/1.50  tff(c_486, plain, (![A_91, B_92]: (k6_setfam_1(A_91, B_92)=k1_setfam_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.43/1.50  tff(c_499, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_486])).
% 3.43/1.50  tff(c_40, plain, (![A_22, B_23]: (k8_setfam_1(A_22, B_23)=k6_setfam_1(A_22, B_23) | k1_xboole_0=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.43/1.50  tff(c_812, plain, (![A_118, B_119]: (k8_setfam_1(A_118, B_119)=k6_setfam_1(A_118, B_119) | B_119='#skF_6' | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(A_118))))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_40])).
% 3.43/1.50  tff(c_831, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_58, c_812])).
% 3.43/1.50  tff(c_839, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_499, c_831])).
% 3.43/1.50  tff(c_840, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_810, c_839])).
% 3.43/1.50  tff(c_841, plain, (~r1_tarski(k1_setfam_1('#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_840, c_503])).
% 3.43/1.50  tff(c_42, plain, (![A_24, B_25]: (m1_subset_1(k8_setfam_1(A_24, B_25), k1_zfmisc_1(A_24)) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.43/1.50  tff(c_845, plain, (m1_subset_1(k1_setfam_1('#skF_7'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_840, c_42])).
% 3.43/1.50  tff(c_849, plain, (m1_subset_1(k1_setfam_1('#skF_7'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_845])).
% 3.43/1.50  tff(c_855, plain, (r1_tarski(k1_setfam_1('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_849, c_46])).
% 3.43/1.50  tff(c_860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_841, c_855])).
% 3.43/1.50  tff(c_862, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_463])).
% 3.43/1.50  tff(c_56, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.43/1.50  tff(c_52, plain, (![B_34, A_33]: (r1_tarski(k1_setfam_1(B_34), k1_setfam_1(A_33)) | k1_xboole_0=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.43/1.50  tff(c_863, plain, (![A_120]: (m1_subset_1(A_120, k1_zfmisc_1('#skF_5')) | ~r2_hidden(A_120, '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_412])).
% 3.43/1.50  tff(c_905, plain, (![A_124]: (r1_tarski(A_124, '#skF_5') | ~r2_hidden(A_124, '#skF_7'))), inference(resolution, [status(thm)], [c_863, c_46])).
% 3.43/1.50  tff(c_920, plain, (r1_tarski('#skF_4'('#skF_7'), '#skF_5') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_28, c_905])).
% 3.43/1.50  tff(c_921, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_920])).
% 3.43/1.50  tff(c_923, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_921, c_862])).
% 3.43/1.50  tff(c_302, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.43/1.50  tff(c_372, plain, (![A_79, B_80]: (r2_hidden('#skF_4'(A_79), B_80) | ~r1_tarski(A_79, B_80) | k1_xboole_0=A_79)), inference(resolution, [status(thm)], [c_28, c_302])).
% 3.43/1.50  tff(c_82, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.43/1.50  tff(c_32, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.43/1.50  tff(c_98, plain, (![A_40]: (k2_xboole_0(k1_xboole_0, A_40)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_82, c_32])).
% 3.43/1.50  tff(c_224, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.43/1.50  tff(c_237, plain, (![B_58]: (k4_xboole_0(B_58, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_58))), inference(superposition, [status(thm), theory('equality')], [c_224, c_98])).
% 3.43/1.50  tff(c_249, plain, (![B_59]: (k4_xboole_0(B_59, k1_xboole_0)=B_59)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_237])).
% 3.43/1.50  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.43/1.50  tff(c_258, plain, (![D_13, B_59]: (~r2_hidden(D_13, k1_xboole_0) | ~r2_hidden(D_13, B_59))), inference(superposition, [status(thm), theory('equality')], [c_249, c_12])).
% 3.43/1.50  tff(c_390, plain, (![A_81, B_82]: (~r2_hidden('#skF_4'(A_81), B_82) | ~r1_tarski(A_81, k1_xboole_0) | k1_xboole_0=A_81)), inference(resolution, [status(thm)], [c_372, c_258])).
% 3.43/1.50  tff(c_398, plain, (![A_14]: (~r1_tarski(A_14, k1_xboole_0) | k1_xboole_0=A_14)), inference(resolution, [status(thm)], [c_28, c_390])).
% 3.43/1.50  tff(c_1133, plain, (![A_140]: (~r1_tarski(A_140, '#skF_7') | A_140='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_921, c_921, c_398])).
% 3.43/1.50  tff(c_1144, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_56, c_1133])).
% 3.43/1.50  tff(c_1152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_923, c_1144])).
% 3.43/1.50  tff(c_1154, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_920])).
% 3.43/1.50  tff(c_871, plain, (![A_121, B_122]: (k6_setfam_1(A_121, B_122)=k1_setfam_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(k1_zfmisc_1(A_121))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.43/1.50  tff(c_888, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_871])).
% 3.43/1.50  tff(c_1396, plain, (![A_170, B_171]: (k8_setfam_1(A_170, B_171)=k6_setfam_1(A_170, B_171) | k1_xboole_0=B_171 | ~m1_subset_1(B_171, k1_zfmisc_1(k1_zfmisc_1(A_170))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.43/1.50  tff(c_1429, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_58, c_1396])).
% 3.43/1.50  tff(c_1446, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_888, c_1429])).
% 3.43/1.50  tff(c_1447, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1154, c_1446])).
% 3.43/1.50  tff(c_887, plain, (k6_setfam_1('#skF_5', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_871])).
% 3.43/1.50  tff(c_1426, plain, (k8_setfam_1('#skF_5', '#skF_6')=k6_setfam_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_60, c_1396])).
% 3.43/1.50  tff(c_1443, plain, (k8_setfam_1('#skF_5', '#skF_6')=k1_setfam_1('#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_887, c_1426])).
% 3.43/1.50  tff(c_1444, plain, (k8_setfam_1('#skF_5', '#skF_6')=k1_setfam_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_862, c_1443])).
% 3.43/1.50  tff(c_1452, plain, (~r1_tarski(k8_setfam_1('#skF_5', '#skF_7'), k1_setfam_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1444, c_54])).
% 3.43/1.50  tff(c_1471, plain, (~r1_tarski(k1_setfam_1('#skF_7'), k1_setfam_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_1452])).
% 3.43/1.50  tff(c_1474, plain, (k1_xboole_0='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_1471])).
% 3.43/1.50  tff(c_1477, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1474])).
% 3.43/1.50  tff(c_1479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_862, c_1477])).
% 3.43/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.50  
% 3.43/1.50  Inference rules
% 3.43/1.50  ----------------------
% 3.43/1.50  #Ref     : 0
% 3.43/1.50  #Sup     : 313
% 3.43/1.50  #Fact    : 0
% 3.43/1.50  #Define  : 0
% 3.43/1.50  #Split   : 4
% 3.43/1.50  #Chain   : 0
% 3.43/1.50  #Close   : 0
% 3.43/1.50  
% 3.43/1.50  Ordering : KBO
% 3.43/1.50  
% 3.43/1.50  Simplification rules
% 3.43/1.50  ----------------------
% 3.43/1.50  #Subsume      : 20
% 3.43/1.50  #Demod        : 153
% 3.43/1.50  #Tautology    : 165
% 3.43/1.50  #SimpNegUnit  : 6
% 3.43/1.50  #BackRed      : 46
% 3.43/1.50  
% 3.43/1.50  #Partial instantiations: 0
% 3.43/1.50  #Strategies tried      : 1
% 3.43/1.50  
% 3.43/1.50  Timing (in seconds)
% 3.43/1.50  ----------------------
% 3.43/1.50  Preprocessing        : 0.32
% 3.43/1.50  Parsing              : 0.17
% 3.43/1.50  CNF conversion       : 0.02
% 3.43/1.50  Main loop            : 0.44
% 3.43/1.50  Inferencing          : 0.16
% 3.43/1.50  Reduction            : 0.14
% 3.43/1.50  Demodulation         : 0.10
% 3.43/1.50  BG Simplification    : 0.02
% 3.43/1.50  Subsumption          : 0.08
% 3.43/1.50  Abstraction          : 0.02
% 3.43/1.50  MUC search           : 0.00
% 3.43/1.50  Cooper               : 0.00
% 3.43/1.50  Total                : 0.80
% 3.43/1.50  Index Insertion      : 0.00
% 3.43/1.50  Index Deletion       : 0.00
% 3.43/1.50  Index Matching       : 0.00
% 3.43/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
