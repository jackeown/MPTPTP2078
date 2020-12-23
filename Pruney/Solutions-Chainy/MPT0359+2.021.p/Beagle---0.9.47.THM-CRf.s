%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:11 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 182 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 252 expanded)
%              Number of equality atoms :   51 ( 122 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_86,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_133,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_59,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_238,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_59])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_240,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_50])).

tff(c_48,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_328,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,A_61)
      | ~ m1_subset_1(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_335,plain,(
    ! [B_60,A_20] :
      ( r1_tarski(B_60,A_20)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_328,c_24])).

tff(c_340,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_335])).

tff(c_352,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_240,c_340])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_357,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_352,c_10])).

tff(c_367,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_380,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_367])).

tff(c_400,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_380])).

tff(c_692,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = k3_subset_1(A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_698,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_240,c_692])).

tff(c_705,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_698])).

tff(c_239,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_133])).

tff(c_707,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_239])).

tff(c_710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_707])).

tff(c_711,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_713,plain,(
    ! [B_82,A_83] : k5_xboole_0(B_82,A_83) = k5_xboole_0(A_83,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_729,plain,(
    ! [A_83] : k5_xboole_0(k1_xboole_0,A_83) = A_83 ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_14])).

tff(c_712,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1049,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,B_113) = k3_subset_1(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1062,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1049])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_xboole_0(k4_xboole_0(A_14,B_15),B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1066,plain,(
    r1_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_18])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( ~ r1_xboole_0(B_13,A_12)
      | ~ r1_tarski(B_13,A_12)
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1072,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | v1_xboole_0(k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1066,c_16])).

tff(c_1075,plain,(
    v1_xboole_0(k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_1072])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1079,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1075,c_6])).

tff(c_1083,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_1062])).

tff(c_1037,plain,(
    ! [B_110,A_111] :
      ( r2_hidden(B_110,A_111)
      | ~ m1_subset_1(B_110,A_111)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1044,plain,(
    ! [B_110,A_20] :
      ( r1_tarski(B_110,A_20)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_1037,c_24])).

tff(c_1106,plain,(
    ! [B_114,A_115] :
      ( r1_tarski(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_115)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1044])).

tff(c_1119,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1106])).

tff(c_1123,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1119,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_910,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1587,plain,(
    ! [B_129,A_130] : k5_xboole_0(B_129,k3_xboole_0(A_130,B_129)) = k4_xboole_0(B_129,A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_910])).

tff(c_1627,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_1587])).

tff(c_1652,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1627])).

tff(c_1132,plain,(
    ! [A_116,B_117,C_118] : k5_xboole_0(k5_xboole_0(A_116,B_117),C_118) = k5_xboole_0(A_116,k5_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1196,plain,(
    ! [A_19,C_118] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_118)) = k5_xboole_0(k1_xboole_0,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1132])).

tff(c_1209,plain,(
    ! [A_19,C_118] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_118)) = C_118 ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_1196])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1218,plain,(
    ! [A_119,C_120] : k5_xboole_0(A_119,k5_xboole_0(A_119,C_120)) = C_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_1196])).

tff(c_1283,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k5_xboole_0(B_122,A_121)) = B_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1218])).

tff(c_1316,plain,(
    ! [A_19,C_118] : k5_xboole_0(k5_xboole_0(A_19,C_118),C_118) = A_19 ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_1283])).

tff(c_1662,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1652,c_1316])).

tff(c_1689,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_1662])).

tff(c_1691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_711,c_1689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.55  
% 3.26/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.26/1.55  
% 3.26/1.55  %Foreground sorts:
% 3.26/1.55  
% 3.26/1.55  
% 3.26/1.55  %Background operators:
% 3.26/1.55  
% 3.26/1.55  
% 3.26/1.55  %Foreground operators:
% 3.26/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.26/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.26/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.26/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.55  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.26/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.55  
% 3.38/1.57  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.38/1.57  tff(f_57, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.38/1.57  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.38/1.57  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.38/1.57  tff(f_86, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.38/1.57  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.38/1.57  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.38/1.57  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.38/1.57  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.38/1.57  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.38/1.57  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.38/1.57  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.38/1.57  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.38/1.57  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.38/1.57  tff(f_33, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.38/1.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.38/1.57  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.38/1.57  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.57  tff(c_22, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.38/1.57  tff(c_44, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.38/1.57  tff(c_52, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.38/1.57  tff(c_60, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 3.38/1.57  tff(c_133, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 3.38/1.57  tff(c_58, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.38/1.57  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 3.38/1.57  tff(c_238, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_133, c_59])).
% 3.38/1.57  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.38/1.57  tff(c_240, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_50])).
% 3.38/1.57  tff(c_48, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.38/1.57  tff(c_328, plain, (![B_60, A_61]: (r2_hidden(B_60, A_61) | ~m1_subset_1(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.38/1.57  tff(c_24, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.38/1.57  tff(c_335, plain, (![B_60, A_20]: (r1_tarski(B_60, A_20) | ~m1_subset_1(B_60, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_328, c_24])).
% 3.38/1.57  tff(c_340, plain, (![B_62, A_63]: (r1_tarski(B_62, A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)))), inference(negUnitSimplification, [status(thm)], [c_48, c_335])).
% 3.38/1.57  tff(c_352, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_240, c_340])).
% 3.38/1.57  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.38/1.57  tff(c_357, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_352, c_10])).
% 3.38/1.57  tff(c_367, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.57  tff(c_380, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_357, c_367])).
% 3.38/1.57  tff(c_400, plain, (k4_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_380])).
% 3.38/1.57  tff(c_692, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=k3_subset_1(A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.38/1.57  tff(c_698, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_240, c_692])).
% 3.38/1.57  tff(c_705, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_400, c_698])).
% 3.38/1.57  tff(c_239, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_133])).
% 3.38/1.57  tff(c_707, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_705, c_239])).
% 3.38/1.57  tff(c_710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_707])).
% 3.38/1.57  tff(c_711, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 3.38/1.57  tff(c_713, plain, (![B_82, A_83]: (k5_xboole_0(B_82, A_83)=k5_xboole_0(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.57  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.38/1.57  tff(c_729, plain, (![A_83]: (k5_xboole_0(k1_xboole_0, A_83)=A_83)), inference(superposition, [status(thm), theory('equality')], [c_713, c_14])).
% 3.38/1.57  tff(c_712, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.38/1.57  tff(c_1049, plain, (![A_112, B_113]: (k4_xboole_0(A_112, B_113)=k3_subset_1(A_112, B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.38/1.57  tff(c_1062, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1049])).
% 3.38/1.57  tff(c_18, plain, (![A_14, B_15]: (r1_xboole_0(k4_xboole_0(A_14, B_15), B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.38/1.57  tff(c_1066, plain, (r1_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1062, c_18])).
% 3.38/1.57  tff(c_16, plain, (![B_13, A_12]: (~r1_xboole_0(B_13, A_12) | ~r1_tarski(B_13, A_12) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.38/1.57  tff(c_1072, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | v1_xboole_0(k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_1066, c_16])).
% 3.38/1.57  tff(c_1075, plain, (v1_xboole_0(k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_1072])).
% 3.38/1.57  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.38/1.57  tff(c_1079, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1075, c_6])).
% 3.38/1.57  tff(c_1083, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_1062])).
% 3.38/1.57  tff(c_1037, plain, (![B_110, A_111]: (r2_hidden(B_110, A_111) | ~m1_subset_1(B_110, A_111) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.38/1.57  tff(c_1044, plain, (![B_110, A_20]: (r1_tarski(B_110, A_20) | ~m1_subset_1(B_110, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_1037, c_24])).
% 3.38/1.57  tff(c_1106, plain, (![B_114, A_115]: (r1_tarski(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(A_115)))), inference(negUnitSimplification, [status(thm)], [c_48, c_1044])).
% 3.38/1.57  tff(c_1119, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1106])).
% 3.38/1.57  tff(c_1123, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1119, c_10])).
% 3.38/1.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.57  tff(c_910, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.38/1.57  tff(c_1587, plain, (![B_129, A_130]: (k5_xboole_0(B_129, k3_xboole_0(A_130, B_129))=k4_xboole_0(B_129, A_130))), inference(superposition, [status(thm), theory('equality')], [c_2, c_910])).
% 3.38/1.57  tff(c_1627, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1123, c_1587])).
% 3.38/1.57  tff(c_1652, plain, (k5_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_1627])).
% 3.38/1.57  tff(c_1132, plain, (![A_116, B_117, C_118]: (k5_xboole_0(k5_xboole_0(A_116, B_117), C_118)=k5_xboole_0(A_116, k5_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.57  tff(c_1196, plain, (![A_19, C_118]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_118))=k5_xboole_0(k1_xboole_0, C_118))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1132])).
% 3.38/1.57  tff(c_1209, plain, (![A_19, C_118]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_118))=C_118)), inference(demodulation, [status(thm), theory('equality')], [c_729, c_1196])).
% 3.38/1.57  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.38/1.57  tff(c_1218, plain, (![A_119, C_120]: (k5_xboole_0(A_119, k5_xboole_0(A_119, C_120))=C_120)), inference(demodulation, [status(thm), theory('equality')], [c_729, c_1196])).
% 3.38/1.57  tff(c_1283, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k5_xboole_0(B_122, A_121))=B_122)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1218])).
% 3.38/1.57  tff(c_1316, plain, (![A_19, C_118]: (k5_xboole_0(k5_xboole_0(A_19, C_118), C_118)=A_19)), inference(superposition, [status(thm), theory('equality')], [c_1209, c_1283])).
% 3.38/1.57  tff(c_1662, plain, (k5_xboole_0(k1_xboole_0, '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1652, c_1316])).
% 3.38/1.57  tff(c_1689, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_729, c_1662])).
% 3.38/1.57  tff(c_1691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_711, c_1689])).
% 3.38/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.57  
% 3.38/1.57  Inference rules
% 3.38/1.57  ----------------------
% 3.38/1.57  #Ref     : 0
% 3.38/1.57  #Sup     : 393
% 3.38/1.57  #Fact    : 0
% 3.38/1.57  #Define  : 0
% 3.38/1.57  #Split   : 1
% 3.38/1.57  #Chain   : 0
% 3.38/1.57  #Close   : 0
% 3.38/1.57  
% 3.38/1.57  Ordering : KBO
% 3.38/1.57  
% 3.38/1.57  Simplification rules
% 3.38/1.57  ----------------------
% 3.38/1.57  #Subsume      : 13
% 3.38/1.57  #Demod        : 184
% 3.38/1.57  #Tautology    : 267
% 3.38/1.57  #SimpNegUnit  : 7
% 3.38/1.57  #BackRed      : 10
% 3.38/1.57  
% 3.38/1.57  #Partial instantiations: 0
% 3.38/1.57  #Strategies tried      : 1
% 3.38/1.57  
% 3.38/1.57  Timing (in seconds)
% 3.38/1.57  ----------------------
% 3.38/1.57  Preprocessing        : 0.32
% 3.38/1.57  Parsing              : 0.16
% 3.38/1.57  CNF conversion       : 0.02
% 3.38/1.57  Main loop            : 0.48
% 3.38/1.57  Inferencing          : 0.17
% 3.38/1.57  Reduction            : 0.19
% 3.38/1.57  Demodulation         : 0.15
% 3.38/1.57  BG Simplification    : 0.02
% 3.38/1.57  Subsumption          : 0.06
% 3.38/1.57  Abstraction          : 0.03
% 3.38/1.57  MUC search           : 0.00
% 3.38/1.57  Cooper               : 0.00
% 3.38/1.57  Total                : 0.85
% 3.38/1.57  Index Insertion      : 0.00
% 3.38/1.57  Index Deletion       : 0.00
% 3.38/1.57  Index Matching       : 0.00
% 3.38/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
