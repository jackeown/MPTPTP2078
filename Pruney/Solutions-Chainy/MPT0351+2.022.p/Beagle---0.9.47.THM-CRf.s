%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:39 EST 2020

% Result     : Theorem 12.83s
% Output     : CNFRefutation 13.01s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 325 expanded)
%              Number of leaves         :   43 ( 124 expanded)
%              Depth                    :   20
%              Number of atoms          :  190 ( 553 expanded)
%              Number of equality atoms :   52 ( 152 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_98,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_100,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_50,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_31230,plain,(
    ! [A_980,B_981] :
      ( r2_hidden('#skF_2'(A_980,B_981),A_980)
      | r1_tarski(A_980,B_981) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    ! [A_42] : k2_subset_1(A_42) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_72,plain,(
    ! [A_43] : m1_subset_1(k2_subset_1(A_43),k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_79,plain,(
    ! [A_43] : m1_subset_1(A_43,k1_zfmisc_1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72])).

tff(c_1321,plain,(
    ! [A_159,B_160,C_161] :
      ( k4_subset_1(A_159,B_160,C_161) = k2_xboole_0(B_160,C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(A_159))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5595,plain,(
    ! [A_333,B_334] :
      ( k4_subset_1(A_333,B_334,A_333) = k2_xboole_0(B_334,A_333)
      | ~ m1_subset_1(B_334,k1_zfmisc_1(A_333)) ) ),
    inference(resolution,[status(thm)],[c_79,c_1321])).

tff(c_5623,plain,(
    k4_subset_1('#skF_7','#skF_8','#skF_7') = k2_xboole_0('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_5595])).

tff(c_76,plain,(
    k4_subset_1('#skF_7','#skF_8',k2_subset_1('#skF_7')) != k2_subset_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_80,plain,(
    k4_subset_1('#skF_7','#skF_8','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_76])).

tff(c_5635,plain,(
    k2_xboole_0('#skF_8','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5623,c_80])).

tff(c_30,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_188,plain,(
    ! [A_71,B_72] : k3_tarski(k2_tarski(A_71,B_72)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_204,plain,(
    ! [B_75,A_76] : k3_tarski(k2_tarski(B_75,A_76)) = k2_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_188])).

tff(c_60,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_210,plain,(
    ! [B_75,A_76] : k2_xboole_0(B_75,A_76) = k2_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_60])).

tff(c_575,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_2'(A_108,B_109),A_108)
      | r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,A_10)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_604,plain,(
    ! [A_10,B_11,B_109] :
      ( r2_hidden('#skF_2'(k4_xboole_0(A_10,B_11),B_109),A_10)
      | r1_tarski(k4_xboole_0(A_10,B_11),B_109) ) ),
    inference(resolution,[status(thm)],[c_575,c_16])).

tff(c_12,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,k4_xboole_0(A_10,B_11))
      | r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_23] : k4_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_361,plain,(
    ! [D_85,B_86,A_87] :
      ( ~ r2_hidden(D_85,B_86)
      | ~ r2_hidden(D_85,k4_xboole_0(A_87,B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_435,plain,(
    ! [D_91,A_92] :
      ( ~ r2_hidden(D_91,A_92)
      | ~ r2_hidden(D_91,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_361])).

tff(c_465,plain,(
    ! [A_97] :
      ( ~ r2_hidden('#skF_1'(A_97),k1_xboole_0)
      | v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_4,c_435])).

tff(c_474,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_465])).

tff(c_227,plain,(
    ! [B_77,A_78] : k2_xboole_0(B_77,A_78) = k2_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_60])).

tff(c_243,plain,(
    ! [A_78] : k2_xboole_0(k1_xboole_0,A_78) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_30])).

tff(c_378,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(B_89,A_88)) = k2_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_385,plain,(
    ! [B_89] : k4_xboole_0(B_89,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_243])).

tff(c_405,plain,(
    ! [B_90] : k4_xboole_0(B_90,k1_xboole_0) = B_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_385])).

tff(c_36,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_417,plain,(
    ! [B_90] : k4_xboole_0(B_90,B_90) = k3_xboole_0(B_90,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_36])).

tff(c_552,plain,(
    ! [D_105,A_106,B_107] :
      ( r2_hidden(D_105,A_106)
      | ~ r2_hidden(D_105,k4_xboole_0(A_106,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_574,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_106,B_107)),A_106)
      | v1_xboole_0(k4_xboole_0(A_106,B_107)) ) ),
    inference(resolution,[status(thm)],[c_4,c_552])).

tff(c_3778,plain,(
    ! [A_286,B_287] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_286,B_287)),B_287)
      | v1_xboole_0(k4_xboole_0(A_286,B_287)) ) ),
    inference(resolution,[status(thm)],[c_4,c_361])).

tff(c_3791,plain,(
    ! [A_106] : v1_xboole_0(k4_xboole_0(A_106,A_106)) ),
    inference(resolution,[status(thm)],[c_574,c_3778])).

tff(c_3835,plain,(
    ! [A_288] : v1_xboole_0(k3_xboole_0(A_288,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_3791])).

tff(c_40,plain,(
    ! [B_25,A_24] :
      ( ~ v1_xboole_0(B_25)
      | B_25 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_477,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_474,c_40])).

tff(c_3895,plain,(
    ! [A_288] : k3_xboole_0(A_288,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3835,c_477])).

tff(c_173,plain,(
    ! [B_68,A_69] :
      ( v1_xboole_0(B_68)
      | ~ m1_subset_1(B_68,A_69)
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_184,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_173])).

tff(c_186,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_312,plain,(
    ! [B_80,A_81] :
      ( r2_hidden(B_80,A_81)
      | ~ m1_subset_1(B_80,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_48,plain,(
    ! [C_37,A_33] :
      ( r1_tarski(C_37,A_33)
      | ~ r2_hidden(C_37,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1854,plain,(
    ! [B_195,A_196] :
      ( r1_tarski(B_195,A_196)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_196))
      | v1_xboole_0(k1_zfmisc_1(A_196)) ) ),
    inference(resolution,[status(thm)],[c_312,c_48])).

tff(c_1871,plain,
    ( r1_tarski('#skF_8','#skF_7')
    | v1_xboole_0(k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_1854])).

tff(c_1882,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_1871])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1897,plain,(
    k3_xboole_0('#skF_8','#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1882,c_32])).

tff(c_324,plain,(
    ! [A_82,B_83] : k4_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2978,plain,(
    ! [A_259,B_260] : k4_xboole_0(A_259,k3_xboole_0(A_259,B_260)) = k3_xboole_0(A_259,k4_xboole_0(A_259,B_260)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_324])).

tff(c_3055,plain,(
    k3_xboole_0('#skF_8',k4_xboole_0('#skF_8','#skF_7')) = k4_xboole_0('#skF_8','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1897,c_2978])).

tff(c_3081,plain,(
    k3_xboole_0('#skF_8',k4_xboole_0('#skF_8','#skF_7')) = k3_xboole_0('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_3055])).

tff(c_3903,plain,(
    k3_xboole_0('#skF_8',k4_xboole_0('#skF_8','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3895,c_3081])).

tff(c_730,plain,(
    ! [D_131,A_132,B_133] :
      ( r2_hidden(D_131,k4_xboole_0(A_132,B_133))
      | r2_hidden(D_131,B_133)
      | ~ r2_hidden(D_131,A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8125,plain,(
    ! [D_429,A_430,B_431] :
      ( r2_hidden(D_429,k3_xboole_0(A_430,B_431))
      | r2_hidden(D_429,k4_xboole_0(A_430,B_431))
      | ~ r2_hidden(D_429,A_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_730])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_29418,plain,(
    ! [D_940,B_941,A_942] :
      ( ~ r2_hidden(D_940,B_941)
      | r2_hidden(D_940,k3_xboole_0(A_942,B_941))
      | ~ r2_hidden(D_940,A_942) ) ),
    inference(resolution,[status(thm)],[c_8125,c_14])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_29597,plain,(
    ! [A_943,B_944,D_945] :
      ( ~ v1_xboole_0(k3_xboole_0(A_943,B_944))
      | ~ r2_hidden(D_945,B_944)
      | ~ r2_hidden(D_945,A_943) ) ),
    inference(resolution,[status(thm)],[c_29418,c_2])).

tff(c_29651,plain,(
    ! [D_945] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_945,k4_xboole_0('#skF_8','#skF_7'))
      | ~ r2_hidden(D_945,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3903,c_29597])).

tff(c_29761,plain,(
    ! [D_949] :
      ( ~ r2_hidden(D_949,k4_xboole_0('#skF_8','#skF_7'))
      | ~ r2_hidden(D_949,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_29651])).

tff(c_29987,plain,(
    ! [D_950] :
      ( r2_hidden(D_950,'#skF_7')
      | ~ r2_hidden(D_950,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_12,c_29761])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30311,plain,(
    ! [A_952] :
      ( r1_tarski(A_952,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_952,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_29987,c_8])).

tff(c_30349,plain,(
    ! [B_953] : r1_tarski(k4_xboole_0('#skF_8',B_953),'#skF_7') ),
    inference(resolution,[status(thm)],[c_604,c_30311])).

tff(c_697,plain,(
    ! [C_125,B_126,A_127] :
      ( r2_hidden(C_125,B_126)
      | ~ r2_hidden(C_125,A_127)
      | ~ r1_tarski(A_127,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_709,plain,(
    ! [A_1,B_126] :
      ( r2_hidden('#skF_1'(A_1),B_126)
      | ~ r1_tarski(A_1,B_126)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_697])).

tff(c_3826,plain,(
    ! [A_286,B_126] :
      ( ~ r1_tarski(k4_xboole_0(A_286,B_126),B_126)
      | v1_xboole_0(k4_xboole_0(A_286,B_126)) ) ),
    inference(resolution,[status(thm)],[c_709,c_3778])).

tff(c_30405,plain,(
    v1_xboole_0(k4_xboole_0('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_30349,c_3826])).

tff(c_30502,plain,(
    k4_xboole_0('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30405,c_477])).

tff(c_34,plain,(
    ! [A_19,B_20] : k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30739,plain,(
    k2_xboole_0('#skF_7',k1_xboole_0) = k2_xboole_0('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_30502,c_34])).

tff(c_30833,plain,(
    k2_xboole_0('#skF_8','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_210,c_30739])).

tff(c_30835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5635,c_30833])).

tff(c_30837,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_157,plain,(
    ! [C_62,A_63] :
      ( r2_hidden(C_62,k1_zfmisc_1(A_63))
      | ~ r1_tarski(C_62,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_161,plain,(
    ! [A_63,C_62] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_63))
      | ~ r1_tarski(C_62,A_63) ) ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_30860,plain,(
    ! [C_62] : ~ r1_tarski(C_62,'#skF_7') ),
    inference(resolution,[status(thm)],[c_30837,c_161])).

tff(c_30836,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_30863,plain,(
    ! [A_957] :
      ( A_957 = '#skF_8'
      | ~ v1_xboole_0(A_957) ) ),
    inference(resolution,[status(thm)],[c_30836,c_40])).

tff(c_30870,plain,(
    k1_zfmisc_1('#skF_7') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30837,c_30863])).

tff(c_30879,plain,(
    ! [C_37] :
      ( r1_tarski(C_37,'#skF_7')
      | ~ r2_hidden(C_37,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30870,c_48])).

tff(c_30890,plain,(
    ! [C_37] : ~ r2_hidden(C_37,'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_30860,c_30879])).

tff(c_31249,plain,(
    ! [B_982] : r1_tarski('#skF_8',B_982) ),
    inference(resolution,[status(thm)],[c_31230,c_30890])).

tff(c_30887,plain,(
    m1_subset_1('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_30870,c_79])).

tff(c_68,plain,(
    ! [B_41,A_40] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30909,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_30887,c_68])).

tff(c_30912,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30836,c_30909])).

tff(c_30840,plain,(
    ! [A_24] :
      ( A_24 = '#skF_8'
      | ~ v1_xboole_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_30836,c_40])).

tff(c_30918,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30912,c_30840])).

tff(c_30923,plain,(
    ! [C_62] : ~ r1_tarski(C_62,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30918,c_30860])).

tff(c_31257,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_31249,c_30923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:45:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.83/5.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.83/5.68  
% 12.83/5.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.83/5.68  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_5
% 12.83/5.68  
% 12.83/5.68  %Foreground sorts:
% 12.83/5.68  
% 12.83/5.68  
% 12.83/5.68  %Background operators:
% 12.83/5.68  
% 12.83/5.68  
% 12.83/5.68  %Foreground operators:
% 12.83/5.68  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 12.83/5.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.83/5.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.83/5.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.83/5.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.83/5.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.83/5.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 12.83/5.68  tff('#skF_7', type, '#skF_7': $i).
% 12.83/5.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.83/5.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.83/5.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.83/5.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.83/5.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.83/5.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.83/5.68  tff('#skF_8', type, '#skF_8': $i).
% 12.83/5.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.83/5.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.83/5.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 12.83/5.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.83/5.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.83/5.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.83/5.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.83/5.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.83/5.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.83/5.68  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 12.83/5.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.83/5.68  
% 13.01/5.71  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.01/5.71  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 13.01/5.71  tff(f_98, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 13.01/5.71  tff(f_100, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 13.01/5.71  tff(f_106, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.01/5.71  tff(f_50, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 13.01/5.71  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.01/5.71  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.01/5.71  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.01/5.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.01/5.71  tff(f_60, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 13.01/5.71  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.01/5.71  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.01/5.71  tff(f_68, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 13.01/5.71  tff(f_96, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 13.01/5.71  tff(f_81, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.01/5.71  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.01/5.71  tff(c_31230, plain, (![A_980, B_981]: (r2_hidden('#skF_2'(A_980, B_981), A_980) | r1_tarski(A_980, B_981))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.01/5.71  tff(c_78, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.01/5.71  tff(c_70, plain, (![A_42]: (k2_subset_1(A_42)=A_42)), inference(cnfTransformation, [status(thm)], [f_98])).
% 13.01/5.71  tff(c_72, plain, (![A_43]: (m1_subset_1(k2_subset_1(A_43), k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.01/5.71  tff(c_79, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72])).
% 13.01/5.71  tff(c_1321, plain, (![A_159, B_160, C_161]: (k4_subset_1(A_159, B_160, C_161)=k2_xboole_0(B_160, C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(A_159)) | ~m1_subset_1(B_160, k1_zfmisc_1(A_159)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.01/5.71  tff(c_5595, plain, (![A_333, B_334]: (k4_subset_1(A_333, B_334, A_333)=k2_xboole_0(B_334, A_333) | ~m1_subset_1(B_334, k1_zfmisc_1(A_333)))), inference(resolution, [status(thm)], [c_79, c_1321])).
% 13.01/5.71  tff(c_5623, plain, (k4_subset_1('#skF_7', '#skF_8', '#skF_7')=k2_xboole_0('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_78, c_5595])).
% 13.01/5.71  tff(c_76, plain, (k4_subset_1('#skF_7', '#skF_8', k2_subset_1('#skF_7'))!=k2_subset_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.01/5.71  tff(c_80, plain, (k4_subset_1('#skF_7', '#skF_8', '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_76])).
% 13.01/5.71  tff(c_5635, plain, (k2_xboole_0('#skF_8', '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5623, c_80])).
% 13.01/5.71  tff(c_30, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.01/5.71  tff(c_42, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.01/5.71  tff(c_188, plain, (![A_71, B_72]: (k3_tarski(k2_tarski(A_71, B_72))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.01/5.71  tff(c_204, plain, (![B_75, A_76]: (k3_tarski(k2_tarski(B_75, A_76))=k2_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_42, c_188])).
% 13.01/5.71  tff(c_60, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.01/5.71  tff(c_210, plain, (![B_75, A_76]: (k2_xboole_0(B_75, A_76)=k2_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_204, c_60])).
% 13.01/5.71  tff(c_575, plain, (![A_108, B_109]: (r2_hidden('#skF_2'(A_108, B_109), A_108) | r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.01/5.71  tff(c_16, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, A_10) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.01/5.71  tff(c_604, plain, (![A_10, B_11, B_109]: (r2_hidden('#skF_2'(k4_xboole_0(A_10, B_11), B_109), A_10) | r1_tarski(k4_xboole_0(A_10, B_11), B_109))), inference(resolution, [status(thm)], [c_575, c_16])).
% 13.01/5.71  tff(c_12, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, k4_xboole_0(A_10, B_11)) | r2_hidden(D_15, B_11) | ~r2_hidden(D_15, A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.01/5.71  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.01/5.71  tff(c_38, plain, (![A_23]: (k4_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.01/5.71  tff(c_361, plain, (![D_85, B_86, A_87]: (~r2_hidden(D_85, B_86) | ~r2_hidden(D_85, k4_xboole_0(A_87, B_86)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.01/5.71  tff(c_435, plain, (![D_91, A_92]: (~r2_hidden(D_91, A_92) | ~r2_hidden(D_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_361])).
% 13.01/5.71  tff(c_465, plain, (![A_97]: (~r2_hidden('#skF_1'(A_97), k1_xboole_0) | v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_4, c_435])).
% 13.01/5.71  tff(c_474, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_465])).
% 13.01/5.71  tff(c_227, plain, (![B_77, A_78]: (k2_xboole_0(B_77, A_78)=k2_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_204, c_60])).
% 13.01/5.71  tff(c_243, plain, (![A_78]: (k2_xboole_0(k1_xboole_0, A_78)=A_78)), inference(superposition, [status(thm), theory('equality')], [c_227, c_30])).
% 13.01/5.71  tff(c_378, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(B_89, A_88))=k2_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.01/5.71  tff(c_385, plain, (![B_89]: (k4_xboole_0(B_89, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_89))), inference(superposition, [status(thm), theory('equality')], [c_378, c_243])).
% 13.01/5.71  tff(c_405, plain, (![B_90]: (k4_xboole_0(B_90, k1_xboole_0)=B_90)), inference(demodulation, [status(thm), theory('equality')], [c_243, c_385])).
% 13.01/5.71  tff(c_36, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.01/5.71  tff(c_417, plain, (![B_90]: (k4_xboole_0(B_90, B_90)=k3_xboole_0(B_90, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_405, c_36])).
% 13.01/5.71  tff(c_552, plain, (![D_105, A_106, B_107]: (r2_hidden(D_105, A_106) | ~r2_hidden(D_105, k4_xboole_0(A_106, B_107)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.01/5.71  tff(c_574, plain, (![A_106, B_107]: (r2_hidden('#skF_1'(k4_xboole_0(A_106, B_107)), A_106) | v1_xboole_0(k4_xboole_0(A_106, B_107)))), inference(resolution, [status(thm)], [c_4, c_552])).
% 13.01/5.71  tff(c_3778, plain, (![A_286, B_287]: (~r2_hidden('#skF_1'(k4_xboole_0(A_286, B_287)), B_287) | v1_xboole_0(k4_xboole_0(A_286, B_287)))), inference(resolution, [status(thm)], [c_4, c_361])).
% 13.01/5.71  tff(c_3791, plain, (![A_106]: (v1_xboole_0(k4_xboole_0(A_106, A_106)))), inference(resolution, [status(thm)], [c_574, c_3778])).
% 13.01/5.71  tff(c_3835, plain, (![A_288]: (v1_xboole_0(k3_xboole_0(A_288, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_3791])).
% 13.01/5.71  tff(c_40, plain, (![B_25, A_24]: (~v1_xboole_0(B_25) | B_25=A_24 | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.01/5.71  tff(c_477, plain, (![A_24]: (k1_xboole_0=A_24 | ~v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_474, c_40])).
% 13.01/5.71  tff(c_3895, plain, (![A_288]: (k3_xboole_0(A_288, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3835, c_477])).
% 13.01/5.71  tff(c_173, plain, (![B_68, A_69]: (v1_xboole_0(B_68) | ~m1_subset_1(B_68, A_69) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.01/5.71  tff(c_184, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_173])).
% 13.01/5.71  tff(c_186, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_184])).
% 13.01/5.71  tff(c_312, plain, (![B_80, A_81]: (r2_hidden(B_80, A_81) | ~m1_subset_1(B_80, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.01/5.71  tff(c_48, plain, (![C_37, A_33]: (r1_tarski(C_37, A_33) | ~r2_hidden(C_37, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.01/5.71  tff(c_1854, plain, (![B_195, A_196]: (r1_tarski(B_195, A_196) | ~m1_subset_1(B_195, k1_zfmisc_1(A_196)) | v1_xboole_0(k1_zfmisc_1(A_196)))), inference(resolution, [status(thm)], [c_312, c_48])).
% 13.01/5.71  tff(c_1871, plain, (r1_tarski('#skF_8', '#skF_7') | v1_xboole_0(k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_1854])).
% 13.01/5.71  tff(c_1882, plain, (r1_tarski('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_186, c_1871])).
% 13.01/5.71  tff(c_32, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.01/5.71  tff(c_1897, plain, (k3_xboole_0('#skF_8', '#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_1882, c_32])).
% 13.01/5.71  tff(c_324, plain, (![A_82, B_83]: (k4_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.01/5.71  tff(c_2978, plain, (![A_259, B_260]: (k4_xboole_0(A_259, k3_xboole_0(A_259, B_260))=k3_xboole_0(A_259, k4_xboole_0(A_259, B_260)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_324])).
% 13.01/5.71  tff(c_3055, plain, (k3_xboole_0('#skF_8', k4_xboole_0('#skF_8', '#skF_7'))=k4_xboole_0('#skF_8', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1897, c_2978])).
% 13.01/5.71  tff(c_3081, plain, (k3_xboole_0('#skF_8', k4_xboole_0('#skF_8', '#skF_7'))=k3_xboole_0('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_417, c_3055])).
% 13.01/5.71  tff(c_3903, plain, (k3_xboole_0('#skF_8', k4_xboole_0('#skF_8', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3895, c_3081])).
% 13.01/5.71  tff(c_730, plain, (![D_131, A_132, B_133]: (r2_hidden(D_131, k4_xboole_0(A_132, B_133)) | r2_hidden(D_131, B_133) | ~r2_hidden(D_131, A_132))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.01/5.71  tff(c_8125, plain, (![D_429, A_430, B_431]: (r2_hidden(D_429, k3_xboole_0(A_430, B_431)) | r2_hidden(D_429, k4_xboole_0(A_430, B_431)) | ~r2_hidden(D_429, A_430))), inference(superposition, [status(thm), theory('equality')], [c_36, c_730])).
% 13.01/5.71  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.01/5.71  tff(c_29418, plain, (![D_940, B_941, A_942]: (~r2_hidden(D_940, B_941) | r2_hidden(D_940, k3_xboole_0(A_942, B_941)) | ~r2_hidden(D_940, A_942))), inference(resolution, [status(thm)], [c_8125, c_14])).
% 13.01/5.71  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.01/5.71  tff(c_29597, plain, (![A_943, B_944, D_945]: (~v1_xboole_0(k3_xboole_0(A_943, B_944)) | ~r2_hidden(D_945, B_944) | ~r2_hidden(D_945, A_943))), inference(resolution, [status(thm)], [c_29418, c_2])).
% 13.01/5.71  tff(c_29651, plain, (![D_945]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(D_945, k4_xboole_0('#skF_8', '#skF_7')) | ~r2_hidden(D_945, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3903, c_29597])).
% 13.01/5.71  tff(c_29761, plain, (![D_949]: (~r2_hidden(D_949, k4_xboole_0('#skF_8', '#skF_7')) | ~r2_hidden(D_949, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_474, c_29651])).
% 13.01/5.71  tff(c_29987, plain, (![D_950]: (r2_hidden(D_950, '#skF_7') | ~r2_hidden(D_950, '#skF_8'))), inference(resolution, [status(thm)], [c_12, c_29761])).
% 13.01/5.71  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.01/5.71  tff(c_30311, plain, (![A_952]: (r1_tarski(A_952, '#skF_7') | ~r2_hidden('#skF_2'(A_952, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_29987, c_8])).
% 13.01/5.71  tff(c_30349, plain, (![B_953]: (r1_tarski(k4_xboole_0('#skF_8', B_953), '#skF_7'))), inference(resolution, [status(thm)], [c_604, c_30311])).
% 13.01/5.71  tff(c_697, plain, (![C_125, B_126, A_127]: (r2_hidden(C_125, B_126) | ~r2_hidden(C_125, A_127) | ~r1_tarski(A_127, B_126))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.01/5.71  tff(c_709, plain, (![A_1, B_126]: (r2_hidden('#skF_1'(A_1), B_126) | ~r1_tarski(A_1, B_126) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_697])).
% 13.01/5.71  tff(c_3826, plain, (![A_286, B_126]: (~r1_tarski(k4_xboole_0(A_286, B_126), B_126) | v1_xboole_0(k4_xboole_0(A_286, B_126)))), inference(resolution, [status(thm)], [c_709, c_3778])).
% 13.01/5.71  tff(c_30405, plain, (v1_xboole_0(k4_xboole_0('#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_30349, c_3826])).
% 13.01/5.71  tff(c_30502, plain, (k4_xboole_0('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_30405, c_477])).
% 13.01/5.71  tff(c_34, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.01/5.71  tff(c_30739, plain, (k2_xboole_0('#skF_7', k1_xboole_0)=k2_xboole_0('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_30502, c_34])).
% 13.01/5.71  tff(c_30833, plain, (k2_xboole_0('#skF_8', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_210, c_30739])).
% 13.01/5.71  tff(c_30835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5635, c_30833])).
% 13.01/5.71  tff(c_30837, plain, (v1_xboole_0(k1_zfmisc_1('#skF_7'))), inference(splitRight, [status(thm)], [c_184])).
% 13.01/5.71  tff(c_157, plain, (![C_62, A_63]: (r2_hidden(C_62, k1_zfmisc_1(A_63)) | ~r1_tarski(C_62, A_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.01/5.71  tff(c_161, plain, (![A_63, C_62]: (~v1_xboole_0(k1_zfmisc_1(A_63)) | ~r1_tarski(C_62, A_63))), inference(resolution, [status(thm)], [c_157, c_2])).
% 13.01/5.71  tff(c_30860, plain, (![C_62]: (~r1_tarski(C_62, '#skF_7'))), inference(resolution, [status(thm)], [c_30837, c_161])).
% 13.01/5.71  tff(c_30836, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_184])).
% 13.01/5.71  tff(c_30863, plain, (![A_957]: (A_957='#skF_8' | ~v1_xboole_0(A_957))), inference(resolution, [status(thm)], [c_30836, c_40])).
% 13.01/5.71  tff(c_30870, plain, (k1_zfmisc_1('#skF_7')='#skF_8'), inference(resolution, [status(thm)], [c_30837, c_30863])).
% 13.01/5.71  tff(c_30879, plain, (![C_37]: (r1_tarski(C_37, '#skF_7') | ~r2_hidden(C_37, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_30870, c_48])).
% 13.01/5.71  tff(c_30890, plain, (![C_37]: (~r2_hidden(C_37, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_30860, c_30879])).
% 13.01/5.71  tff(c_31249, plain, (![B_982]: (r1_tarski('#skF_8', B_982))), inference(resolution, [status(thm)], [c_31230, c_30890])).
% 13.01/5.71  tff(c_30887, plain, (m1_subset_1('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_30870, c_79])).
% 13.01/5.71  tff(c_68, plain, (![B_41, A_40]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.01/5.71  tff(c_30909, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_30887, c_68])).
% 13.01/5.71  tff(c_30912, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30836, c_30909])).
% 13.01/5.71  tff(c_30840, plain, (![A_24]: (A_24='#skF_8' | ~v1_xboole_0(A_24))), inference(resolution, [status(thm)], [c_30836, c_40])).
% 13.01/5.71  tff(c_30918, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_30912, c_30840])).
% 13.01/5.71  tff(c_30923, plain, (![C_62]: (~r1_tarski(C_62, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_30918, c_30860])).
% 13.01/5.71  tff(c_31257, plain, $false, inference(resolution, [status(thm)], [c_31249, c_30923])).
% 13.01/5.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.01/5.71  
% 13.01/5.71  Inference rules
% 13.01/5.71  ----------------------
% 13.01/5.71  #Ref     : 0
% 13.01/5.71  #Sup     : 7775
% 13.01/5.71  #Fact    : 0
% 13.01/5.71  #Define  : 0
% 13.01/5.71  #Split   : 20
% 13.01/5.71  #Chain   : 0
% 13.01/5.71  #Close   : 0
% 13.01/5.71  
% 13.01/5.71  Ordering : KBO
% 13.01/5.71  
% 13.01/5.71  Simplification rules
% 13.01/5.71  ----------------------
% 13.01/5.71  #Subsume      : 2318
% 13.01/5.71  #Demod        : 4355
% 13.01/5.71  #Tautology    : 2286
% 13.01/5.71  #SimpNegUnit  : 371
% 13.01/5.71  #BackRed      : 178
% 13.01/5.71  
% 13.01/5.71  #Partial instantiations: 0
% 13.01/5.71  #Strategies tried      : 1
% 13.01/5.71  
% 13.01/5.71  Timing (in seconds)
% 13.01/5.71  ----------------------
% 13.01/5.71  Preprocessing        : 0.34
% 13.01/5.71  Parsing              : 0.18
% 13.01/5.71  CNF conversion       : 0.03
% 13.01/5.71  Main loop            : 4.52
% 13.01/5.71  Inferencing          : 0.99
% 13.01/5.71  Reduction            : 1.60
% 13.01/5.71  Demodulation         : 1.17
% 13.01/5.71  BG Simplification    : 0.11
% 13.01/5.71  Subsumption          : 1.50
% 13.01/5.71  Abstraction          : 0.16
% 13.01/5.71  MUC search           : 0.00
% 13.01/5.71  Cooper               : 0.00
% 13.01/5.71  Total                : 4.91
% 13.01/5.71  Index Insertion      : 0.00
% 13.01/5.71  Index Deletion       : 0.00
% 13.01/5.71  Index Matching       : 0.00
% 13.01/5.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
