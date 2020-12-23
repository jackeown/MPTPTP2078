%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:32 EST 2020

% Result     : Theorem 14.54s
% Output     : CNFRefutation 14.70s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 227 expanded)
%              Number of leaves         :   48 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 254 expanded)
%              Number of equality atoms :   68 ( 171 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_98,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_60,plain,(
    ! [A_62] : k2_subset_1(A_62) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_73,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_70])).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1629,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k3_subset_1(A_147,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1646,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1629])).

tff(c_66,plain,(
    ! [A_67] : ~ v1_xboole_0(k1_zfmisc_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_373,plain,(
    ! [B_103,A_104] :
      ( r2_hidden(B_103,A_104)
      | ~ m1_subset_1(B_103,A_104)
      | v1_xboole_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ! [C_57,A_53] :
      ( r1_tarski(C_57,A_53)
      | ~ r2_hidden(C_57,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_377,plain,(
    ! [B_103,A_53] :
      ( r1_tarski(B_103,A_53)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_53))
      | v1_xboole_0(k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_373,c_38])).

tff(c_392,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(B_107,A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_108)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_377])).

tff(c_401,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_392])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_405,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_401,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_419,plain,(
    ! [A_111,B_112] : k5_xboole_0(A_111,k3_xboole_0(A_111,B_112)) = k4_xboole_0(A_111,B_112) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_586,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k3_xboole_0(B_122,A_121)) = k4_xboole_0(A_121,B_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_419])).

tff(c_607,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_586])).

tff(c_156,plain,(
    ! [B_84,A_85] : k5_xboole_0(B_84,A_85) = k5_xboole_0(A_85,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_172,plain,(
    ! [A_85] : k5_xboole_0(k1_xboole_0,A_85) = A_85 ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_20])).

tff(c_18,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_451,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_419])).

tff(c_461,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_451])).

tff(c_1023,plain,(
    ! [A_136,B_137,C_138] : k5_xboole_0(k5_xboole_0(A_136,B_137),C_138) = k5_xboole_0(A_136,k5_xboole_0(B_137,C_138)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1089,plain,(
    ! [A_12,C_138] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_138)) = k5_xboole_0(k1_xboole_0,C_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_1023])).

tff(c_1132,plain,(
    ! [A_12,C_138] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_138)) = C_138 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_1089])).

tff(c_1136,plain,(
    ! [A_139,C_140] : k5_xboole_0(A_139,k5_xboole_0(A_139,C_140)) = C_140 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_1089])).

tff(c_1219,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k5_xboole_0(B_142,A_141)) = B_142 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1136])).

tff(c_1453,plain,(
    ! [A_145,C_146] : k5_xboole_0(k5_xboole_0(A_145,C_146),C_146) = A_145 ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_1219])).

tff(c_1529,plain,(
    k5_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_1453])).

tff(c_1791,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1646,c_1529])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_253,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = A_91
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_842,plain,(
    ! [A_130,B_131] : k3_xboole_0(k4_xboole_0(A_130,B_131),A_130) = k4_xboole_0(A_130,B_131) ),
    inference(resolution,[status(thm)],[c_16,c_253])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_854,plain,(
    ! [A_130,B_131] : k5_xboole_0(k4_xboole_0(A_130,B_131),k4_xboole_0(A_130,B_131)) = k4_xboole_0(k4_xboole_0(A_130,B_131),A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_8])).

tff(c_897,plain,(
    ! [A_130,B_131] : k4_xboole_0(k4_xboole_0(A_130,B_131),A_130) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_854])).

tff(c_1657,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_897])).

tff(c_1650,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1646,c_607])).

tff(c_1200,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1136])).

tff(c_1222,plain,(
    ! [B_142,A_141] : k5_xboole_0(k5_xboole_0(B_142,A_141),B_142) = A_141 ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_1200])).

tff(c_1738,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_1222])).

tff(c_445,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_419])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1903,plain,(
    ! [A_153,B_154,C_155] : k5_xboole_0(k3_xboole_0(A_153,B_154),k3_xboole_0(C_155,B_154)) = k3_xboole_0(k5_xboole_0(A_153,C_155),B_154) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2018,plain,(
    ! [A_5,C_155] : k5_xboole_0(A_5,k3_xboole_0(C_155,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_155),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1903])).

tff(c_2162,plain,(
    ! [A_160,C_161] : k3_xboole_0(A_160,k5_xboole_0(A_160,C_161)) = k4_xboole_0(A_160,C_161) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_2,c_2018])).

tff(c_2190,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1738,c_2162])).

tff(c_2256,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1657,c_2,c_2190])).

tff(c_24,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2288,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')),k1_xboole_0) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2256,c_24])).

tff(c_2299,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1791,c_2288])).

tff(c_64,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k3_subset_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3379,plain,(
    ! [A_191,B_192,C_193] :
      ( k4_subset_1(A_191,B_192,C_193) = k2_xboole_0(B_192,C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(A_191))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(A_191)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46926,plain,(
    ! [A_520,B_521,B_522] :
      ( k4_subset_1(A_520,B_521,k3_subset_1(A_520,B_522)) = k2_xboole_0(B_521,k3_subset_1(A_520,B_522))
      | ~ m1_subset_1(B_521,k1_zfmisc_1(A_520))
      | ~ m1_subset_1(B_522,k1_zfmisc_1(A_520)) ) ),
    inference(resolution,[status(thm)],[c_64,c_3379])).

tff(c_46955,plain,(
    ! [B_523] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_523)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_523))
      | ~ m1_subset_1(B_523,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_72,c_46926])).

tff(c_46978,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_46955])).

tff(c_46990,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2299,c_46978])).

tff(c_46992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_46990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.54/8.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.54/8.25  
% 14.54/8.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.54/8.26  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 14.54/8.26  
% 14.54/8.26  %Foreground sorts:
% 14.54/8.26  
% 14.54/8.26  
% 14.54/8.26  %Background operators:
% 14.54/8.26  
% 14.54/8.26  
% 14.54/8.26  %Foreground operators:
% 14.54/8.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.54/8.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.54/8.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.54/8.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.54/8.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.54/8.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.54/8.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.54/8.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.54/8.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.54/8.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 14.54/8.26  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.54/8.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.54/8.26  tff('#skF_3', type, '#skF_3': $i).
% 14.54/8.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.54/8.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.54/8.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.54/8.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.54/8.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.54/8.26  tff('#skF_4', type, '#skF_4': $i).
% 14.54/8.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.54/8.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.54/8.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.54/8.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.54/8.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.54/8.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.54/8.26  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 14.54/8.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.54/8.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.54/8.26  
% 14.70/8.27  tff(f_87, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 14.70/8.27  tff(f_109, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 14.70/8.27  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 14.70/8.27  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 14.70/8.27  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 14.70/8.27  tff(f_98, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 14.70/8.27  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 14.70/8.27  tff(f_70, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 14.70/8.27  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.70/8.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.70/8.27  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.70/8.27  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 14.70/8.27  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 14.70/8.27  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 14.70/8.27  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 14.70/8.27  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 14.70/8.27  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 14.70/8.27  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 14.70/8.27  tff(f_95, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 14.70/8.27  tff(f_104, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 14.70/8.27  tff(c_60, plain, (![A_62]: (k2_subset_1(A_62)=A_62)), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.70/8.27  tff(c_70, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.70/8.27  tff(c_73, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_70])).
% 14.70/8.27  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.70/8.27  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.70/8.27  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.70/8.27  tff(c_1629, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k3_subset_1(A_147, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.70/8.27  tff(c_1646, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_1629])).
% 14.70/8.27  tff(c_66, plain, (![A_67]: (~v1_xboole_0(k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.70/8.27  tff(c_373, plain, (![B_103, A_104]: (r2_hidden(B_103, A_104) | ~m1_subset_1(B_103, A_104) | v1_xboole_0(A_104))), inference(cnfTransformation, [status(thm)], [f_85])).
% 14.70/8.27  tff(c_38, plain, (![C_57, A_53]: (r1_tarski(C_57, A_53) | ~r2_hidden(C_57, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.70/8.27  tff(c_377, plain, (![B_103, A_53]: (r1_tarski(B_103, A_53) | ~m1_subset_1(B_103, k1_zfmisc_1(A_53)) | v1_xboole_0(k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_373, c_38])).
% 14.70/8.27  tff(c_392, plain, (![B_107, A_108]: (r1_tarski(B_107, A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(A_108)))), inference(negUnitSimplification, [status(thm)], [c_66, c_377])).
% 14.70/8.27  tff(c_401, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_392])).
% 14.70/8.27  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.70/8.27  tff(c_405, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_401, c_14])).
% 14.70/8.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.70/8.27  tff(c_419, plain, (![A_111, B_112]: (k5_xboole_0(A_111, k3_xboole_0(A_111, B_112))=k4_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.70/8.27  tff(c_586, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k3_xboole_0(B_122, A_121))=k4_xboole_0(A_121, B_122))), inference(superposition, [status(thm), theory('equality')], [c_2, c_419])).
% 14.70/8.27  tff(c_607, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_405, c_586])).
% 14.70/8.27  tff(c_156, plain, (![B_84, A_85]: (k5_xboole_0(B_84, A_85)=k5_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.70/8.27  tff(c_172, plain, (![A_85]: (k5_xboole_0(k1_xboole_0, A_85)=A_85)), inference(superposition, [status(thm), theory('equality')], [c_156, c_20])).
% 14.70/8.27  tff(c_18, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.70/8.27  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.70/8.27  tff(c_451, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k5_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_419])).
% 14.70/8.27  tff(c_461, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_451])).
% 14.70/8.27  tff(c_1023, plain, (![A_136, B_137, C_138]: (k5_xboole_0(k5_xboole_0(A_136, B_137), C_138)=k5_xboole_0(A_136, k5_xboole_0(B_137, C_138)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.70/8.27  tff(c_1089, plain, (![A_12, C_138]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_138))=k5_xboole_0(k1_xboole_0, C_138))), inference(superposition, [status(thm), theory('equality')], [c_461, c_1023])).
% 14.70/8.27  tff(c_1132, plain, (![A_12, C_138]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_138))=C_138)), inference(demodulation, [status(thm), theory('equality')], [c_172, c_1089])).
% 14.70/8.27  tff(c_1136, plain, (![A_139, C_140]: (k5_xboole_0(A_139, k5_xboole_0(A_139, C_140))=C_140)), inference(demodulation, [status(thm), theory('equality')], [c_172, c_1089])).
% 14.70/8.27  tff(c_1219, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k5_xboole_0(B_142, A_141))=B_142)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1136])).
% 14.70/8.27  tff(c_1453, plain, (![A_145, C_146]: (k5_xboole_0(k5_xboole_0(A_145, C_146), C_146)=A_145)), inference(superposition, [status(thm), theory('equality')], [c_1132, c_1219])).
% 14.70/8.27  tff(c_1529, plain, (k5_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_607, c_1453])).
% 14.70/8.27  tff(c_1791, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1646, c_1529])).
% 14.70/8.27  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.70/8.27  tff(c_253, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=A_91 | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.70/8.27  tff(c_842, plain, (![A_130, B_131]: (k3_xboole_0(k4_xboole_0(A_130, B_131), A_130)=k4_xboole_0(A_130, B_131))), inference(resolution, [status(thm)], [c_16, c_253])).
% 14.70/8.27  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.70/8.27  tff(c_854, plain, (![A_130, B_131]: (k5_xboole_0(k4_xboole_0(A_130, B_131), k4_xboole_0(A_130, B_131))=k4_xboole_0(k4_xboole_0(A_130, B_131), A_130))), inference(superposition, [status(thm), theory('equality')], [c_842, c_8])).
% 14.70/8.27  tff(c_897, plain, (![A_130, B_131]: (k4_xboole_0(k4_xboole_0(A_130, B_131), A_130)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_461, c_854])).
% 14.70/8.27  tff(c_1657, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1646, c_897])).
% 14.70/8.27  tff(c_1650, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1646, c_607])).
% 14.70/8.27  tff(c_1200, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1136])).
% 14.70/8.27  tff(c_1222, plain, (![B_142, A_141]: (k5_xboole_0(k5_xboole_0(B_142, A_141), B_142)=A_141)), inference(superposition, [status(thm), theory('equality')], [c_1219, c_1200])).
% 14.70/8.27  tff(c_1738, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1650, c_1222])).
% 14.70/8.27  tff(c_445, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_419])).
% 14.70/8.27  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.70/8.27  tff(c_1903, plain, (![A_153, B_154, C_155]: (k5_xboole_0(k3_xboole_0(A_153, B_154), k3_xboole_0(C_155, B_154))=k3_xboole_0(k5_xboole_0(A_153, C_155), B_154))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.70/8.27  tff(c_2018, plain, (![A_5, C_155]: (k5_xboole_0(A_5, k3_xboole_0(C_155, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_155), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1903])).
% 14.70/8.27  tff(c_2162, plain, (![A_160, C_161]: (k3_xboole_0(A_160, k5_xboole_0(A_160, C_161))=k4_xboole_0(A_160, C_161))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_2, c_2018])).
% 14.70/8.27  tff(c_2190, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1738, c_2162])).
% 14.70/8.27  tff(c_2256, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1657, c_2, c_2190])).
% 14.70/8.27  tff(c_24, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.70/8.27  tff(c_2288, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')), k1_xboole_0)=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2256, c_24])).
% 14.70/8.27  tff(c_2299, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1791, c_2288])).
% 14.70/8.27  tff(c_64, plain, (![A_65, B_66]: (m1_subset_1(k3_subset_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.70/8.27  tff(c_3379, plain, (![A_191, B_192, C_193]: (k4_subset_1(A_191, B_192, C_193)=k2_xboole_0(B_192, C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(A_191)) | ~m1_subset_1(B_192, k1_zfmisc_1(A_191)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.70/8.27  tff(c_46926, plain, (![A_520, B_521, B_522]: (k4_subset_1(A_520, B_521, k3_subset_1(A_520, B_522))=k2_xboole_0(B_521, k3_subset_1(A_520, B_522)) | ~m1_subset_1(B_521, k1_zfmisc_1(A_520)) | ~m1_subset_1(B_522, k1_zfmisc_1(A_520)))), inference(resolution, [status(thm)], [c_64, c_3379])).
% 14.70/8.27  tff(c_46955, plain, (![B_523]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_523))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_523)) | ~m1_subset_1(B_523, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_72, c_46926])).
% 14.70/8.27  tff(c_46978, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_46955])).
% 14.70/8.27  tff(c_46990, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2299, c_46978])).
% 14.70/8.27  tff(c_46992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_46990])).
% 14.70/8.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.70/8.27  
% 14.70/8.27  Inference rules
% 14.70/8.27  ----------------------
% 14.70/8.27  #Ref     : 0
% 14.70/8.27  #Sup     : 11803
% 14.70/8.27  #Fact    : 0
% 14.70/8.27  #Define  : 0
% 14.70/8.27  #Split   : 0
% 14.70/8.27  #Chain   : 0
% 14.70/8.27  #Close   : 0
% 14.70/8.27  
% 14.70/8.27  Ordering : KBO
% 14.70/8.27  
% 14.70/8.27  Simplification rules
% 14.70/8.27  ----------------------
% 14.70/8.27  #Subsume      : 224
% 14.70/8.27  #Demod        : 17714
% 14.70/8.27  #Tautology    : 6778
% 14.70/8.27  #SimpNegUnit  : 22
% 14.70/8.27  #BackRed      : 17
% 14.70/8.27  
% 14.70/8.27  #Partial instantiations: 0
% 14.70/8.27  #Strategies tried      : 1
% 14.70/8.27  
% 14.70/8.27  Timing (in seconds)
% 14.70/8.27  ----------------------
% 14.70/8.28  Preprocessing        : 0.34
% 14.70/8.28  Parsing              : 0.17
% 14.70/8.28  CNF conversion       : 0.02
% 14.70/8.28  Main loop            : 7.12
% 14.70/8.28  Inferencing          : 0.93
% 14.70/8.28  Reduction            : 4.63
% 14.70/8.28  Demodulation         : 4.25
% 14.70/8.28  BG Simplification    : 0.13
% 14.70/8.28  Subsumption          : 1.16
% 14.70/8.28  Abstraction          : 0.22
% 14.70/8.28  MUC search           : 0.00
% 14.70/8.28  Cooper               : 0.00
% 14.70/8.28  Total                : 7.50
% 14.70/8.28  Index Insertion      : 0.00
% 14.70/8.28  Index Deletion       : 0.00
% 14.70/8.28  Index Matching       : 0.00
% 14.70/8.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
