%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:33 EST 2020

% Result     : Theorem 18.59s
% Output     : CNFRefutation 18.73s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 583 expanded)
%              Number of leaves         :   46 ( 220 expanded)
%              Depth                    :   19
%              Number of atoms          :  155 ( 833 expanded)
%              Number of equality atoms :   94 ( 385 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_83,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_94,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_56,plain,(
    ! [A_56] : k2_subset_1(A_56) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_66,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_69,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_359,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k4_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_385,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_359])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_892,plain,(
    ! [A_123,B_124,C_125] : k5_xboole_0(k5_xboole_0(A_123,B_124),C_125) = k5_xboole_0(A_123,k5_xboole_0(B_124,C_125)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_962,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k5_xboole_0(B_19,k3_xboole_0(A_18,B_19))) = k2_xboole_0(A_18,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_892])).

tff(c_1014,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_962])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_529,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k3_xboole_0(A_108,B_109)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5873,plain,(
    ! [A_229,B_230] : k5_xboole_0(k5_xboole_0(A_229,B_230),k3_xboole_0(B_230,A_229)) = k2_xboole_0(B_230,A_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_529])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k5_xboole_0(k5_xboole_0(A_14,B_15),C_16) = k5_xboole_0(A_14,k5_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5915,plain,(
    ! [A_229,B_230] : k5_xboole_0(A_229,k5_xboole_0(B_230,k3_xboole_0(B_230,A_229))) = k2_xboole_0(B_230,A_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_5873,c_16])).

tff(c_6113,plain,(
    ! [B_230,A_229] : k2_xboole_0(B_230,A_229) = k2_xboole_0(A_229,B_230) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_6,c_5915])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_736,plain,(
    ! [A_114,B_115] :
      ( k4_xboole_0(A_114,B_115) = k3_subset_1(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_749,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_736])).

tff(c_62,plain,(
    ! [A_61] : ~ v1_xboole_0(k1_zfmisc_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_333,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,A_92)
      | ~ m1_subset_1(B_91,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [C_51,A_47] :
      ( r1_tarski(C_51,A_47)
      | ~ r2_hidden(C_51,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_337,plain,(
    ! [B_91,A_47] :
      ( r1_tarski(B_91,A_47)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_47))
      | v1_xboole_0(k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_333,c_34])).

tff(c_341,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(B_93,A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_337])).

tff(c_350,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_341])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_354,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_350,c_10])).

tff(c_448,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k3_xboole_0(B_104,A_103)) = k4_xboole_0(A_103,B_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_359])).

tff(c_469,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_448])).

tff(c_752,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_469])).

tff(c_140,plain,(
    ! [B_72,A_73] : k5_xboole_0(B_72,A_73) = k5_xboole_0(A_73,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_156,plain,(
    ! [A_73] : k5_xboole_0(k1_xboole_0,A_73) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_14])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1003,plain,(
    ! [A_17,C_125] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_125)) = k5_xboole_0(k1_xboole_0,C_125) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_892])).

tff(c_1226,plain,(
    ! [A_136,C_137] : k5_xboole_0(A_136,k5_xboole_0(A_136,C_137)) = C_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1003])).

tff(c_1325,plain,(
    ! [A_138,B_139] : k5_xboole_0(A_138,k5_xboole_0(B_139,A_138)) = B_139 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1226])).

tff(c_1395,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_1325])).

tff(c_12,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ! [C_51,A_47] :
      ( r2_hidden(C_51,k1_zfmisc_1(A_47))
      | ~ r1_tarski(C_51,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_428,plain,(
    ! [B_99,A_100] :
      ( m1_subset_1(B_99,A_100)
      | ~ r2_hidden(B_99,A_100)
      | v1_xboole_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_434,plain,(
    ! [C_51,A_47] :
      ( m1_subset_1(C_51,k1_zfmisc_1(A_47))
      | v1_xboole_0(k1_zfmisc_1(A_47))
      | ~ r1_tarski(C_51,A_47) ) ),
    inference(resolution,[status(thm)],[c_36,c_428])).

tff(c_438,plain,(
    ! [C_51,A_47] :
      ( m1_subset_1(C_51,k1_zfmisc_1(A_47))
      | ~ r1_tarski(C_51,A_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_434])).

tff(c_237,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_242,plain,(
    ! [A_77] : k3_xboole_0(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_237])).

tff(c_247,plain,(
    ! [A_77] : k3_xboole_0(A_77,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_2])).

tff(c_375,plain,(
    ! [A_77] : k5_xboole_0(A_77,k1_xboole_0) = k4_xboole_0(A_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_359])).

tff(c_393,plain,(
    ! [A_77] : k4_xboole_0(A_77,k1_xboole_0) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_375])).

tff(c_858,plain,(
    ! [A_119,C_120] :
      ( k4_xboole_0(A_119,C_120) = k3_subset_1(A_119,C_120)
      | ~ r1_tarski(C_120,A_119) ) ),
    inference(resolution,[status(thm)],[c_438,c_736])).

tff(c_864,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = k3_subset_1(A_12,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_858])).

tff(c_869,plain,(
    ! [A_121] : k3_subset_1(A_121,k1_xboole_0) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_864])).

tff(c_60,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k3_subset_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_881,plain,(
    ! [A_122] :
      ( m1_subset_1(A_122,k1_zfmisc_1(A_122))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_122)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_60])).

tff(c_884,plain,(
    ! [A_47] :
      ( m1_subset_1(A_47,k1_zfmisc_1(A_47))
      | ~ r1_tarski(k1_xboole_0,A_47) ) ),
    inference(resolution,[status(thm)],[c_438,c_881])).

tff(c_1020,plain,(
    ! [A_126] : m1_subset_1(A_126,k1_zfmisc_1(A_126)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_884])).

tff(c_340,plain,(
    ! [B_91,A_47] :
      ( r1_tarski(B_91,A_47)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_337])).

tff(c_1033,plain,(
    ! [A_127] : r1_tarski(A_127,A_127) ),
    inference(resolution,[status(thm)],[c_1020,c_340])).

tff(c_1041,plain,(
    ! [A_127] : k3_xboole_0(A_127,A_127) = A_127 ),
    inference(resolution,[status(thm)],[c_1033,c_10])).

tff(c_1725,plain,(
    ! [A_144,B_145,C_146] : k5_xboole_0(k3_xboole_0(A_144,B_145),k3_xboole_0(C_146,B_145)) = k3_xboole_0(k5_xboole_0(A_144,C_146),B_145) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1776,plain,(
    ! [C_146] : k5_xboole_0('#skF_4',k3_xboole_0(C_146,'#skF_3')) = k3_xboole_0(k5_xboole_0('#skF_4',C_146),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_1725])).

tff(c_1925,plain,(
    ! [C_147] : k5_xboole_0('#skF_4',k3_xboole_0(C_147,'#skF_3')) = k3_xboole_0('#skF_3',k5_xboole_0('#skF_4',C_147)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1776])).

tff(c_1018,plain,(
    ! [A_17,C_125] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_125)) = C_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1003])).

tff(c_1365,plain,(
    ! [A_17,C_125] : k5_xboole_0(k5_xboole_0(A_17,C_125),C_125) = A_17 ),
    inference(superposition,[status(thm),theory(equality)],[c_1018,c_1325])).

tff(c_3638,plain,(
    ! [C_202] : k5_xboole_0(k3_xboole_0('#skF_3',k5_xboole_0('#skF_4',C_202)),k3_xboole_0(C_202,'#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1925,c_1365])).

tff(c_3688,plain,(
    k5_xboole_0(k3_xboole_0('#skF_3','#skF_3'),k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_3638])).

tff(c_3761,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1041,c_2,c_3688])).

tff(c_241,plain,(
    ! [A_12] : k3_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_237])).

tff(c_568,plain,(
    ! [A_12] : k5_xboole_0(k5_xboole_0(k1_xboole_0,A_12),k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_529])).

tff(c_604,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_156,c_568])).

tff(c_644,plain,(
    ! [A_112] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_112,A_112)) = k2_xboole_0(A_112,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_529])).

tff(c_650,plain,(
    ! [A_112] : k5_xboole_0(k2_xboole_0(A_112,A_112),k3_xboole_0(k1_xboole_0,k3_xboole_0(A_112,A_112))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_112,A_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_20])).

tff(c_685,plain,(
    ! [A_112] : k3_xboole_0(A_112,A_112) = k2_xboole_0(A_112,A_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_14,c_241,c_650])).

tff(c_1042,plain,(
    ! [A_112] : k2_xboole_0(A_112,A_112) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_685])).

tff(c_695,plain,(
    ! [A_113] : k3_xboole_0(A_113,A_113) = k2_xboole_0(A_113,A_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_14,c_241,c_650])).

tff(c_707,plain,(
    ! [A_113] : k5_xboole_0(A_113,k2_xboole_0(A_113,A_113)) = k4_xboole_0(A_113,A_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_6])).

tff(c_1158,plain,(
    ! [A_113] : k5_xboole_0(A_113,A_113) = k4_xboole_0(A_113,A_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1042,c_707])).

tff(c_1159,plain,(
    ! [A_113] : k4_xboole_0(A_113,A_113) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1158])).

tff(c_499,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_4])).

tff(c_751,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_499])).

tff(c_956,plain,(
    ! [C_125] : k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),C_125) = k5_xboole_0('#skF_3',k5_xboole_0('#skF_4',C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_892])).

tff(c_1779,plain,(
    ! [A_144] : k5_xboole_0(k3_xboole_0(A_144,'#skF_3'),'#skF_4') = k3_xboole_0(k5_xboole_0(A_144,'#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_1725])).

tff(c_2082,plain,(
    ! [A_152] : k5_xboole_0(k3_xboole_0(A_152,'#skF_3'),'#skF_4') = k3_xboole_0('#skF_3',k5_xboole_0(A_152,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1779])).

tff(c_2153,plain,(
    ! [A_155] : k5_xboole_0(k3_xboole_0('#skF_3',k5_xboole_0(A_155,'#skF_4')),'#skF_4') = k3_xboole_0(A_155,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2082,c_1365])).

tff(c_2207,plain,(
    k5_xboole_0(k3_xboole_0('#skF_3',k5_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_4'))),'#skF_4') = k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_2153])).

tff(c_2247,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_1041,c_4,c_2,c_14,c_18,c_2207])).

tff(c_1750,plain,(
    ! [A_144,B_145] : k3_xboole_0(k5_xboole_0(A_144,k3_xboole_0(A_144,B_145)),B_145) = k4_xboole_0(k3_xboole_0(A_144,B_145),B_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_1725,c_6])).

tff(c_1815,plain,(
    ! [A_144,B_145] : k4_xboole_0(k3_xboole_0(A_144,B_145),B_145) = k3_xboole_0(B_145,k4_xboole_0(A_144,B_145)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6,c_1750])).

tff(c_9177,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4'))) = k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2247,c_1815])).

tff(c_9229,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3761,c_1159,c_9177])).

tff(c_586,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_529])).

tff(c_9249,plain,(
    k5_xboole_0(k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4'),k1_xboole_0) = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9229,c_586])).

tff(c_9306,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6113,c_1395,c_14,c_4,c_9249])).

tff(c_3844,plain,(
    ! [A_203,B_204,C_205] :
      ( k4_subset_1(A_203,B_204,C_205) = k2_xboole_0(B_204,C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(A_203))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(A_203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_47961,plain,(
    ! [A_449,B_450,B_451] :
      ( k4_subset_1(A_449,B_450,k3_subset_1(A_449,B_451)) = k2_xboole_0(B_450,k3_subset_1(A_449,B_451))
      | ~ m1_subset_1(B_450,k1_zfmisc_1(A_449))
      | ~ m1_subset_1(B_451,k1_zfmisc_1(A_449)) ) ),
    inference(resolution,[status(thm)],[c_60,c_3844])).

tff(c_47995,plain,(
    ! [B_452] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_452)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_452))
      | ~ m1_subset_1(B_452,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_68,c_47961])).

tff(c_48026,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_47995])).

tff(c_48042,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9306,c_48026])).

tff(c_48044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_48042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:38:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.59/11.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.59/11.27  
% 18.59/11.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.59/11.27  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 18.59/11.27  
% 18.59/11.27  %Foreground sorts:
% 18.59/11.27  
% 18.59/11.27  
% 18.59/11.27  %Background operators:
% 18.59/11.27  
% 18.59/11.27  
% 18.59/11.27  %Foreground operators:
% 18.59/11.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.59/11.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.59/11.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.59/11.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.59/11.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.59/11.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.59/11.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.59/11.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.59/11.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.59/11.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 18.59/11.27  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 18.59/11.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.59/11.27  tff('#skF_3', type, '#skF_3': $i).
% 18.59/11.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.59/11.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.59/11.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.59/11.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.59/11.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.59/11.27  tff('#skF_4', type, '#skF_4': $i).
% 18.59/11.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.59/11.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 18.59/11.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.59/11.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.59/11.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.59/11.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 18.59/11.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 18.59/11.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.59/11.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.59/11.27  
% 18.73/11.29  tff(f_83, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 18.73/11.29  tff(f_105, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 18.73/11.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.73/11.29  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 18.73/11.29  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 18.73/11.29  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 18.73/11.29  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 18.73/11.29  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 18.73/11.29  tff(f_94, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 18.73/11.29  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 18.73/11.29  tff(f_66, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 18.73/11.29  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 18.73/11.29  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 18.73/11.29  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 18.73/11.29  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.73/11.29  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 18.73/11.29  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 18.73/11.29  tff(f_100, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 18.73/11.29  tff(c_56, plain, (![A_56]: (k2_subset_1(A_56)=A_56)), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.73/11.29  tff(c_66, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 18.73/11.29  tff(c_69, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_66])).
% 18.73/11.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.73/11.29  tff(c_359, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k4_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.73/11.29  tff(c_385, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_359])).
% 18.73/11.29  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.73/11.29  tff(c_892, plain, (![A_123, B_124, C_125]: (k5_xboole_0(k5_xboole_0(A_123, B_124), C_125)=k5_xboole_0(A_123, k5_xboole_0(B_124, C_125)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.73/11.29  tff(c_962, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k5_xboole_0(B_19, k3_xboole_0(A_18, B_19)))=k2_xboole_0(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_892])).
% 18.73/11.29  tff(c_1014, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_385, c_962])).
% 18.73/11.29  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.73/11.29  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.73/11.29  tff(c_529, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k3_xboole_0(A_108, B_109))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.73/11.29  tff(c_5873, plain, (![A_229, B_230]: (k5_xboole_0(k5_xboole_0(A_229, B_230), k3_xboole_0(B_230, A_229))=k2_xboole_0(B_230, A_229))), inference(superposition, [status(thm), theory('equality')], [c_4, c_529])).
% 18.73/11.29  tff(c_16, plain, (![A_14, B_15, C_16]: (k5_xboole_0(k5_xboole_0(A_14, B_15), C_16)=k5_xboole_0(A_14, k5_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.73/11.29  tff(c_5915, plain, (![A_229, B_230]: (k5_xboole_0(A_229, k5_xboole_0(B_230, k3_xboole_0(B_230, A_229)))=k2_xboole_0(B_230, A_229))), inference(superposition, [status(thm), theory('equality')], [c_5873, c_16])).
% 18.73/11.29  tff(c_6113, plain, (![B_230, A_229]: (k2_xboole_0(B_230, A_229)=k2_xboole_0(A_229, B_230))), inference(demodulation, [status(thm), theory('equality')], [c_1014, c_6, c_5915])).
% 18.73/11.29  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 18.73/11.29  tff(c_736, plain, (![A_114, B_115]: (k4_xboole_0(A_114, B_115)=k3_subset_1(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.73/11.29  tff(c_749, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_736])).
% 18.73/11.29  tff(c_62, plain, (![A_61]: (~v1_xboole_0(k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 18.73/11.29  tff(c_333, plain, (![B_91, A_92]: (r2_hidden(B_91, A_92) | ~m1_subset_1(B_91, A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.73/11.29  tff(c_34, plain, (![C_51, A_47]: (r1_tarski(C_51, A_47) | ~r2_hidden(C_51, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.73/11.29  tff(c_337, plain, (![B_91, A_47]: (r1_tarski(B_91, A_47) | ~m1_subset_1(B_91, k1_zfmisc_1(A_47)) | v1_xboole_0(k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_333, c_34])).
% 18.73/11.29  tff(c_341, plain, (![B_93, A_94]: (r1_tarski(B_93, A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)))), inference(negUnitSimplification, [status(thm)], [c_62, c_337])).
% 18.73/11.29  tff(c_350, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_341])).
% 18.73/11.29  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.73/11.29  tff(c_354, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_350, c_10])).
% 18.73/11.29  tff(c_448, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k3_xboole_0(B_104, A_103))=k4_xboole_0(A_103, B_104))), inference(superposition, [status(thm), theory('equality')], [c_2, c_359])).
% 18.73/11.29  tff(c_469, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_354, c_448])).
% 18.73/11.29  tff(c_752, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_469])).
% 18.73/11.29  tff(c_140, plain, (![B_72, A_73]: (k5_xboole_0(B_72, A_73)=k5_xboole_0(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.73/11.29  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.73/11.29  tff(c_156, plain, (![A_73]: (k5_xboole_0(k1_xboole_0, A_73)=A_73)), inference(superposition, [status(thm), theory('equality')], [c_140, c_14])).
% 18.73/11.29  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.73/11.29  tff(c_1003, plain, (![A_17, C_125]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_125))=k5_xboole_0(k1_xboole_0, C_125))), inference(superposition, [status(thm), theory('equality')], [c_18, c_892])).
% 18.73/11.29  tff(c_1226, plain, (![A_136, C_137]: (k5_xboole_0(A_136, k5_xboole_0(A_136, C_137))=C_137)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1003])).
% 18.73/11.29  tff(c_1325, plain, (![A_138, B_139]: (k5_xboole_0(A_138, k5_xboole_0(B_139, A_138))=B_139)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1226])).
% 18.73/11.29  tff(c_1395, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_752, c_1325])).
% 18.73/11.29  tff(c_12, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.73/11.29  tff(c_36, plain, (![C_51, A_47]: (r2_hidden(C_51, k1_zfmisc_1(A_47)) | ~r1_tarski(C_51, A_47))), inference(cnfTransformation, [status(thm)], [f_66])).
% 18.73/11.29  tff(c_428, plain, (![B_99, A_100]: (m1_subset_1(B_99, A_100) | ~r2_hidden(B_99, A_100) | v1_xboole_0(A_100))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.73/11.29  tff(c_434, plain, (![C_51, A_47]: (m1_subset_1(C_51, k1_zfmisc_1(A_47)) | v1_xboole_0(k1_zfmisc_1(A_47)) | ~r1_tarski(C_51, A_47))), inference(resolution, [status(thm)], [c_36, c_428])).
% 18.73/11.29  tff(c_438, plain, (![C_51, A_47]: (m1_subset_1(C_51, k1_zfmisc_1(A_47)) | ~r1_tarski(C_51, A_47))), inference(negUnitSimplification, [status(thm)], [c_62, c_434])).
% 18.73/11.29  tff(c_237, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.73/11.29  tff(c_242, plain, (![A_77]: (k3_xboole_0(k1_xboole_0, A_77)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_237])).
% 18.73/11.29  tff(c_247, plain, (![A_77]: (k3_xboole_0(A_77, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_242, c_2])).
% 18.73/11.29  tff(c_375, plain, (![A_77]: (k5_xboole_0(A_77, k1_xboole_0)=k4_xboole_0(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_247, c_359])).
% 18.73/11.29  tff(c_393, plain, (![A_77]: (k4_xboole_0(A_77, k1_xboole_0)=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_375])).
% 18.73/11.29  tff(c_858, plain, (![A_119, C_120]: (k4_xboole_0(A_119, C_120)=k3_subset_1(A_119, C_120) | ~r1_tarski(C_120, A_119))), inference(resolution, [status(thm)], [c_438, c_736])).
% 18.73/11.29  tff(c_864, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=k3_subset_1(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_858])).
% 18.73/11.29  tff(c_869, plain, (![A_121]: (k3_subset_1(A_121, k1_xboole_0)=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_393, c_864])).
% 18.73/11.29  tff(c_60, plain, (![A_59, B_60]: (m1_subset_1(k3_subset_1(A_59, B_60), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.73/11.29  tff(c_881, plain, (![A_122]: (m1_subset_1(A_122, k1_zfmisc_1(A_122)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_122)))), inference(superposition, [status(thm), theory('equality')], [c_869, c_60])).
% 18.73/11.29  tff(c_884, plain, (![A_47]: (m1_subset_1(A_47, k1_zfmisc_1(A_47)) | ~r1_tarski(k1_xboole_0, A_47))), inference(resolution, [status(thm)], [c_438, c_881])).
% 18.73/11.29  tff(c_1020, plain, (![A_126]: (m1_subset_1(A_126, k1_zfmisc_1(A_126)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_884])).
% 18.73/11.29  tff(c_340, plain, (![B_91, A_47]: (r1_tarski(B_91, A_47) | ~m1_subset_1(B_91, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_62, c_337])).
% 18.73/11.29  tff(c_1033, plain, (![A_127]: (r1_tarski(A_127, A_127))), inference(resolution, [status(thm)], [c_1020, c_340])).
% 18.73/11.29  tff(c_1041, plain, (![A_127]: (k3_xboole_0(A_127, A_127)=A_127)), inference(resolution, [status(thm)], [c_1033, c_10])).
% 18.73/11.29  tff(c_1725, plain, (![A_144, B_145, C_146]: (k5_xboole_0(k3_xboole_0(A_144, B_145), k3_xboole_0(C_146, B_145))=k3_xboole_0(k5_xboole_0(A_144, C_146), B_145))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.73/11.29  tff(c_1776, plain, (![C_146]: (k5_xboole_0('#skF_4', k3_xboole_0(C_146, '#skF_3'))=k3_xboole_0(k5_xboole_0('#skF_4', C_146), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_354, c_1725])).
% 18.73/11.29  tff(c_1925, plain, (![C_147]: (k5_xboole_0('#skF_4', k3_xboole_0(C_147, '#skF_3'))=k3_xboole_0('#skF_3', k5_xboole_0('#skF_4', C_147)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1776])).
% 18.73/11.29  tff(c_1018, plain, (![A_17, C_125]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_125))=C_125)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1003])).
% 18.73/11.29  tff(c_1365, plain, (![A_17, C_125]: (k5_xboole_0(k5_xboole_0(A_17, C_125), C_125)=A_17)), inference(superposition, [status(thm), theory('equality')], [c_1018, c_1325])).
% 18.73/11.29  tff(c_3638, plain, (![C_202]: (k5_xboole_0(k3_xboole_0('#skF_3', k5_xboole_0('#skF_4', C_202)), k3_xboole_0(C_202, '#skF_3'))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1925, c_1365])).
% 18.73/11.29  tff(c_3688, plain, (k5_xboole_0(k3_xboole_0('#skF_3', '#skF_3'), k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1395, c_3638])).
% 18.73/11.29  tff(c_3761, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1041, c_2, c_3688])).
% 18.73/11.29  tff(c_241, plain, (![A_12]: (k3_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_237])).
% 18.73/11.29  tff(c_568, plain, (![A_12]: (k5_xboole_0(k5_xboole_0(k1_xboole_0, A_12), k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_241, c_529])).
% 18.73/11.29  tff(c_604, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_156, c_568])).
% 18.73/11.29  tff(c_644, plain, (![A_112]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_112, A_112))=k2_xboole_0(A_112, A_112))), inference(superposition, [status(thm), theory('equality')], [c_18, c_529])).
% 18.73/11.29  tff(c_650, plain, (![A_112]: (k5_xboole_0(k2_xboole_0(A_112, A_112), k3_xboole_0(k1_xboole_0, k3_xboole_0(A_112, A_112)))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_112, A_112)))), inference(superposition, [status(thm), theory('equality')], [c_644, c_20])).
% 18.73/11.29  tff(c_685, plain, (![A_112]: (k3_xboole_0(A_112, A_112)=k2_xboole_0(A_112, A_112))), inference(demodulation, [status(thm), theory('equality')], [c_604, c_14, c_241, c_650])).
% 18.73/11.29  tff(c_1042, plain, (![A_112]: (k2_xboole_0(A_112, A_112)=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_685])).
% 18.73/11.29  tff(c_695, plain, (![A_113]: (k3_xboole_0(A_113, A_113)=k2_xboole_0(A_113, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_604, c_14, c_241, c_650])).
% 18.73/11.29  tff(c_707, plain, (![A_113]: (k5_xboole_0(A_113, k2_xboole_0(A_113, A_113))=k4_xboole_0(A_113, A_113))), inference(superposition, [status(thm), theory('equality')], [c_695, c_6])).
% 18.73/11.29  tff(c_1158, plain, (![A_113]: (k5_xboole_0(A_113, A_113)=k4_xboole_0(A_113, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_1042, c_707])).
% 18.73/11.29  tff(c_1159, plain, (![A_113]: (k4_xboole_0(A_113, A_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1158])).
% 18.73/11.29  tff(c_499, plain, (k5_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_469, c_4])).
% 18.73/11.29  tff(c_751, plain, (k5_xboole_0('#skF_4', '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_499])).
% 18.73/11.29  tff(c_956, plain, (![C_125]: (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), C_125)=k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', C_125)))), inference(superposition, [status(thm), theory('equality')], [c_752, c_892])).
% 18.73/11.29  tff(c_1779, plain, (![A_144]: (k5_xboole_0(k3_xboole_0(A_144, '#skF_3'), '#skF_4')=k3_xboole_0(k5_xboole_0(A_144, '#skF_4'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_354, c_1725])).
% 18.73/11.29  tff(c_2082, plain, (![A_152]: (k5_xboole_0(k3_xboole_0(A_152, '#skF_3'), '#skF_4')=k3_xboole_0('#skF_3', k5_xboole_0(A_152, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1779])).
% 18.73/11.29  tff(c_2153, plain, (![A_155]: (k5_xboole_0(k3_xboole_0('#skF_3', k5_xboole_0(A_155, '#skF_4')), '#skF_4')=k3_xboole_0(A_155, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2082, c_1365])).
% 18.73/11.29  tff(c_2207, plain, (k5_xboole_0(k3_xboole_0('#skF_3', k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_4'))), '#skF_4')=k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_956, c_2153])).
% 18.73/11.29  tff(c_2247, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_1041, c_4, c_2, c_14, c_18, c_2207])).
% 18.73/11.29  tff(c_1750, plain, (![A_144, B_145]: (k3_xboole_0(k5_xboole_0(A_144, k3_xboole_0(A_144, B_145)), B_145)=k4_xboole_0(k3_xboole_0(A_144, B_145), B_145))), inference(superposition, [status(thm), theory('equality')], [c_1725, c_6])).
% 18.73/11.29  tff(c_1815, plain, (![A_144, B_145]: (k4_xboole_0(k3_xboole_0(A_144, B_145), B_145)=k3_xboole_0(B_145, k4_xboole_0(A_144, B_145)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6, c_1750])).
% 18.73/11.29  tff(c_9177, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4')))=k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2247, c_1815])).
% 18.73/11.29  tff(c_9229, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3761, c_1159, c_9177])).
% 18.73/11.29  tff(c_586, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_529])).
% 18.73/11.29  tff(c_9249, plain, (k5_xboole_0(k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4'), k1_xboole_0)=k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9229, c_586])).
% 18.73/11.29  tff(c_9306, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6113, c_1395, c_14, c_4, c_9249])).
% 18.73/11.29  tff(c_3844, plain, (![A_203, B_204, C_205]: (k4_subset_1(A_203, B_204, C_205)=k2_xboole_0(B_204, C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(A_203)) | ~m1_subset_1(B_204, k1_zfmisc_1(A_203)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 18.73/11.29  tff(c_47961, plain, (![A_449, B_450, B_451]: (k4_subset_1(A_449, B_450, k3_subset_1(A_449, B_451))=k2_xboole_0(B_450, k3_subset_1(A_449, B_451)) | ~m1_subset_1(B_450, k1_zfmisc_1(A_449)) | ~m1_subset_1(B_451, k1_zfmisc_1(A_449)))), inference(resolution, [status(thm)], [c_60, c_3844])).
% 18.73/11.29  tff(c_47995, plain, (![B_452]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_452))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_452)) | ~m1_subset_1(B_452, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_68, c_47961])).
% 18.73/11.29  tff(c_48026, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_68, c_47995])).
% 18.73/11.29  tff(c_48042, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9306, c_48026])).
% 18.73/11.29  tff(c_48044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_48042])).
% 18.73/11.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.73/11.29  
% 18.73/11.29  Inference rules
% 18.73/11.29  ----------------------
% 18.73/11.29  #Ref     : 0
% 18.73/11.29  #Sup     : 12465
% 18.73/11.29  #Fact    : 0
% 18.73/11.29  #Define  : 0
% 18.73/11.29  #Split   : 0
% 18.73/11.29  #Chain   : 0
% 18.73/11.29  #Close   : 0
% 18.73/11.29  
% 18.73/11.29  Ordering : KBO
% 18.73/11.29  
% 18.73/11.29  Simplification rules
% 18.73/11.29  ----------------------
% 18.73/11.29  #Subsume      : 485
% 18.73/11.29  #Demod        : 17220
% 18.73/11.29  #Tautology    : 4244
% 18.73/11.29  #SimpNegUnit  : 24
% 18.73/11.29  #BackRed      : 13
% 18.73/11.29  
% 18.73/11.29  #Partial instantiations: 0
% 18.73/11.29  #Strategies tried      : 1
% 18.73/11.29  
% 18.73/11.29  Timing (in seconds)
% 18.73/11.29  ----------------------
% 18.73/11.30  Preprocessing        : 0.35
% 18.73/11.30  Parsing              : 0.18
% 18.73/11.30  CNF conversion       : 0.02
% 18.73/11.30  Main loop            : 10.17
% 18.73/11.30  Inferencing          : 1.10
% 18.73/11.30  Reduction            : 7.18
% 18.73/11.30  Demodulation         : 6.75
% 18.73/11.30  BG Simplification    : 0.20
% 18.73/11.30  Subsumption          : 1.40
% 18.73/11.30  Abstraction          : 0.31
% 18.73/11.30  MUC search           : 0.00
% 18.73/11.30  Cooper               : 0.00
% 18.73/11.30  Total                : 10.57
% 18.73/11.30  Index Insertion      : 0.00
% 18.73/11.30  Index Deletion       : 0.00
% 18.73/11.30  Index Matching       : 0.00
% 18.73/11.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
