%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:54 EST 2020

% Result     : Theorem 7.78s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 504 expanded)
%              Number of leaves         :   42 ( 192 expanded)
%              Depth                    :   18
%              Number of atoms          :  146 ( 901 expanded)
%              Number of equality atoms :   52 ( 378 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_5 > #skF_6 > #skF_1 > #skF_11 > #skF_8 > #skF_4 > #skF_10 > #skF_2 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_108,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_91,axiom,(
    ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_88,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_82,plain,(
    k9_relat_1('#skF_11','#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_86,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_5'(A_25),A_25)
      | v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_116,plain,(
    ! [C_57,B_58] : ~ r2_hidden(C_57,k4_xboole_0(B_58,k1_tarski(C_57))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_120,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_116])).

tff(c_125,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_62,c_120])).

tff(c_78,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_70,plain,(
    ! [A_48] : k8_relat_1(A_48,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_235,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_84,B_85)),A_84)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_247,plain,(
    ! [A_48] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),A_48)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_235])).

tff(c_272,plain,(
    ! [A_86] : r1_tarski(k1_xboole_0,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_78,c_247])).

tff(c_42,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_283,plain,(
    ! [A_87] : k2_xboole_0(k1_xboole_0,A_87) = A_87 ),
    inference(resolution,[status(thm)],[c_272,c_42])).

tff(c_48,plain,(
    ! [A_19,B_20] : k4_xboole_0(k2_xboole_0(A_19,B_20),B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_289,plain,(
    ! [A_87] : k4_xboole_0(k1_xboole_0,A_87) = k4_xboole_0(A_87,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_48])).

tff(c_294,plain,(
    ! [A_87] : k4_xboole_0(A_87,A_87) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_289])).

tff(c_36,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_3'(A_7,B_8,C_9),A_7)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2711,plain,(
    ! [A_245,B_246,C_247] :
      ( r2_hidden('#skF_3'(A_245,B_246,C_247),A_245)
      | r2_hidden('#skF_4'(A_245,B_246,C_247),C_247)
      | k4_xboole_0(A_245,B_246) = C_247 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),B_8)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2718,plain,(
    ! [A_245,C_247] :
      ( r2_hidden('#skF_4'(A_245,A_245,C_247),C_247)
      | k4_xboole_0(A_245,A_245) = C_247 ) ),
    inference(resolution,[status(thm)],[c_2711,c_34])).

tff(c_2791,plain,(
    ! [A_245,C_247] :
      ( r2_hidden('#skF_4'(A_245,A_245,C_247),C_247)
      | k1_xboole_0 = C_247 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_2718])).

tff(c_119,plain,(
    ! [C_57] : ~ r2_hidden(C_57,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_116])).

tff(c_84,plain,(
    r1_tarski('#skF_10',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_164,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,B_66) = k1_xboole_0
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_168,plain,(
    k4_xboole_0('#skF_10',k1_relat_1('#skF_11')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_164])).

tff(c_580,plain,(
    ! [D_118,A_119,B_120] :
      ( r2_hidden(D_118,k4_xboole_0(A_119,B_120))
      | r2_hidden(D_118,B_120)
      | ~ r2_hidden(D_118,A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_602,plain,(
    ! [D_118] :
      ( r2_hidden(D_118,k1_xboole_0)
      | r2_hidden(D_118,k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_118,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_580])).

tff(c_611,plain,(
    ! [D_118] :
      ( r2_hidden(D_118,k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_118,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_602])).

tff(c_6126,plain,(
    ! [A_367,B_368,C_369] :
      ( ~ r2_hidden('#skF_3'(A_367,B_368,C_369),B_368)
      | r2_hidden('#skF_4'(A_367,B_368,C_369),B_368)
      | ~ r2_hidden('#skF_4'(A_367,B_368,C_369),A_367)
      | k4_xboole_0(A_367,B_368) = C_369 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6240,plain,(
    ! [B_373,C_374] :
      ( ~ r2_hidden('#skF_3'(k1_relat_1('#skF_11'),B_373,C_374),B_373)
      | r2_hidden('#skF_4'(k1_relat_1('#skF_11'),B_373,C_374),B_373)
      | k4_xboole_0(k1_relat_1('#skF_11'),B_373) = C_374
      | ~ r2_hidden('#skF_4'(k1_relat_1('#skF_11'),B_373,C_374),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_611,c_6126])).

tff(c_6255,plain,
    ( ~ r2_hidden('#skF_3'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11'))
    | r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11'))
    | k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_11')) = '#skF_10'
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_2791,c_6240])).

tff(c_6271,plain,
    ( ~ r2_hidden('#skF_3'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11'))
    | r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11'))
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_6255])).

tff(c_6272,plain,
    ( ~ r2_hidden('#skF_3'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11'))
    | r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_86,c_6271])).

tff(c_6759,plain,(
    ~ r2_hidden('#skF_3'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_6272])).

tff(c_6762,plain,
    ( r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),'#skF_10')
    | k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_11')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_36,c_6759])).

tff(c_6767,plain,
    ( r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),'#skF_10')
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_6762])).

tff(c_6768,plain,(
    r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6767])).

tff(c_342,plain,(
    ! [B_95,A_96] :
      ( r1_xboole_0(k1_relat_1(B_95),A_96)
      | k9_relat_1(B_95,A_96) != k1_xboole_0
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1089,plain,(
    ! [B_148,A_149] :
      ( k3_xboole_0(k1_relat_1(B_148),A_149) = k1_xboole_0
      | k9_relat_1(B_148,A_149) != k1_xboole_0
      | ~ v1_relat_1(B_148) ) ),
    inference(resolution,[status(thm)],[c_342,c_38])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1109,plain,(
    ! [D_6,A_149,B_148] :
      ( r2_hidden(D_6,k1_xboole_0)
      | ~ r2_hidden(D_6,A_149)
      | ~ r2_hidden(D_6,k1_relat_1(B_148))
      | k9_relat_1(B_148,A_149) != k1_xboole_0
      | ~ v1_relat_1(B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1089,c_2])).

tff(c_1125,plain,(
    ! [D_6,A_149,B_148] :
      ( ~ r2_hidden(D_6,A_149)
      | ~ r2_hidden(D_6,k1_relat_1(B_148))
      | k9_relat_1(B_148,A_149) != k1_xboole_0
      | ~ v1_relat_1(B_148) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_1109])).

tff(c_8528,plain,(
    ! [B_426] :
      ( ~ r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1(B_426))
      | k9_relat_1(B_426,'#skF_10') != k1_xboole_0
      | ~ v1_relat_1(B_426) ) ),
    inference(resolution,[status(thm)],[c_6768,c_1125])).

tff(c_8532,plain,
    ( k9_relat_1('#skF_11','#skF_10') != k1_xboole_0
    | ~ v1_relat_1('#skF_11')
    | ~ r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_611,c_8528])).

tff(c_8539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6768,c_88,c_82,c_8532])).

tff(c_8540,plain,(
    r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_6272])).

tff(c_8541,plain,(
    r2_hidden('#skF_3'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_6272])).

tff(c_8570,plain,
    ( r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),'#skF_10')
    | k4_xboole_0(k1_relat_1('#skF_11'),k1_relat_1('#skF_11')) = '#skF_10' ),
    inference(resolution,[status(thm)],[c_8541,c_34])).

tff(c_8578,plain,
    ( r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),'#skF_10')
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_8570])).

tff(c_8579,plain,(
    r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_8578])).

tff(c_10369,plain,(
    ! [B_452] :
      ( ~ r2_hidden('#skF_4'(k1_relat_1('#skF_11'),k1_relat_1('#skF_11'),'#skF_10'),k1_relat_1(B_452))
      | k9_relat_1(B_452,'#skF_10') != k1_xboole_0
      | ~ v1_relat_1(B_452) ) ),
    inference(resolution,[status(thm)],[c_8579,c_1125])).

tff(c_10372,plain,
    ( k9_relat_1('#skF_11','#skF_10') != k1_xboole_0
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_8540,c_10369])).

tff(c_10383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_10372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.78/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/2.71  
% 7.78/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/2.71  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_5 > #skF_6 > #skF_1 > #skF_11 > #skF_8 > #skF_4 > #skF_10 > #skF_2 > #skF_3 > #skF_7
% 7.78/2.71  
% 7.78/2.71  %Foreground sorts:
% 7.78/2.71  
% 7.78/2.71  
% 7.78/2.71  %Background operators:
% 7.78/2.71  
% 7.78/2.71  
% 7.78/2.71  %Foreground operators:
% 7.78/2.71  tff('#skF_9', type, '#skF_9': $i > $i).
% 7.78/2.71  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.78/2.71  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.78/2.71  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.78/2.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.78/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.78/2.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.78/2.71  tff('#skF_11', type, '#skF_11': $i).
% 7.78/2.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.78/2.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.78/2.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.78/2.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.78/2.71  tff('#skF_8', type, '#skF_8': $i > $i).
% 7.78/2.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.78/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.78/2.71  tff('#skF_10', type, '#skF_10': $i).
% 7.78/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.78/2.71  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.78/2.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.78/2.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.78/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.78/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.78/2.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.78/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.78/2.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.78/2.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.78/2.71  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.78/2.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.78/2.71  
% 7.78/2.73  tff(f_119, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 7.78/2.73  tff(f_60, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 7.78/2.73  tff(f_77, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 7.78/2.73  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 7.78/2.73  tff(f_108, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.78/2.73  tff(f_91, axiom, (![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 7.78/2.73  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 7.78/2.73  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.78/2.73  tff(f_58, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 7.78/2.73  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.78/2.73  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 7.78/2.73  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 7.78/2.73  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 7.78/2.73  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.78/2.73  tff(c_88, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.78/2.73  tff(c_82, plain, (k9_relat_1('#skF_11', '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.78/2.73  tff(c_86, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.78/2.73  tff(c_50, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.78/2.73  tff(c_62, plain, (![A_25]: (r2_hidden('#skF_5'(A_25), A_25) | v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.78/2.73  tff(c_116, plain, (![C_57, B_58]: (~r2_hidden(C_57, k4_xboole_0(B_58, k1_tarski(C_57))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.78/2.73  tff(c_120, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_116])).
% 7.78/2.73  tff(c_125, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_120])).
% 7.78/2.73  tff(c_78, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.78/2.73  tff(c_70, plain, (![A_48]: (k8_relat_1(A_48, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.78/2.73  tff(c_235, plain, (![A_84, B_85]: (r1_tarski(k2_relat_1(k8_relat_1(A_84, B_85)), A_84) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.78/2.73  tff(c_247, plain, (![A_48]: (r1_tarski(k2_relat_1(k1_xboole_0), A_48) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_235])).
% 7.78/2.73  tff(c_272, plain, (![A_86]: (r1_tarski(k1_xboole_0, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_78, c_247])).
% 7.78/2.73  tff(c_42, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.78/2.73  tff(c_283, plain, (![A_87]: (k2_xboole_0(k1_xboole_0, A_87)=A_87)), inference(resolution, [status(thm)], [c_272, c_42])).
% 7.78/2.73  tff(c_48, plain, (![A_19, B_20]: (k4_xboole_0(k2_xboole_0(A_19, B_20), B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.78/2.73  tff(c_289, plain, (![A_87]: (k4_xboole_0(k1_xboole_0, A_87)=k4_xboole_0(A_87, A_87))), inference(superposition, [status(thm), theory('equality')], [c_283, c_48])).
% 7.78/2.73  tff(c_294, plain, (![A_87]: (k4_xboole_0(A_87, A_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_289])).
% 7.78/2.73  tff(c_36, plain, (![A_7, B_8, C_9]: (r2_hidden('#skF_3'(A_7, B_8, C_9), A_7) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.78/2.73  tff(c_2711, plain, (![A_245, B_246, C_247]: (r2_hidden('#skF_3'(A_245, B_246, C_247), A_245) | r2_hidden('#skF_4'(A_245, B_246, C_247), C_247) | k4_xboole_0(A_245, B_246)=C_247)), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.78/2.73  tff(c_34, plain, (![A_7, B_8, C_9]: (~r2_hidden('#skF_3'(A_7, B_8, C_9), B_8) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.78/2.73  tff(c_2718, plain, (![A_245, C_247]: (r2_hidden('#skF_4'(A_245, A_245, C_247), C_247) | k4_xboole_0(A_245, A_245)=C_247)), inference(resolution, [status(thm)], [c_2711, c_34])).
% 7.78/2.73  tff(c_2791, plain, (![A_245, C_247]: (r2_hidden('#skF_4'(A_245, A_245, C_247), C_247) | k1_xboole_0=C_247)), inference(demodulation, [status(thm), theory('equality')], [c_294, c_2718])).
% 7.78/2.73  tff(c_119, plain, (![C_57]: (~r2_hidden(C_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_116])).
% 7.78/2.73  tff(c_84, plain, (r1_tarski('#skF_10', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.78/2.73  tff(c_164, plain, (![A_65, B_66]: (k4_xboole_0(A_65, B_66)=k1_xboole_0 | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.78/2.73  tff(c_168, plain, (k4_xboole_0('#skF_10', k1_relat_1('#skF_11'))=k1_xboole_0), inference(resolution, [status(thm)], [c_84, c_164])).
% 7.78/2.73  tff(c_580, plain, (![D_118, A_119, B_120]: (r2_hidden(D_118, k4_xboole_0(A_119, B_120)) | r2_hidden(D_118, B_120) | ~r2_hidden(D_118, A_119))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.78/2.73  tff(c_602, plain, (![D_118]: (r2_hidden(D_118, k1_xboole_0) | r2_hidden(D_118, k1_relat_1('#skF_11')) | ~r2_hidden(D_118, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_168, c_580])).
% 7.78/2.73  tff(c_611, plain, (![D_118]: (r2_hidden(D_118, k1_relat_1('#skF_11')) | ~r2_hidden(D_118, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_119, c_602])).
% 7.78/2.73  tff(c_6126, plain, (![A_367, B_368, C_369]: (~r2_hidden('#skF_3'(A_367, B_368, C_369), B_368) | r2_hidden('#skF_4'(A_367, B_368, C_369), B_368) | ~r2_hidden('#skF_4'(A_367, B_368, C_369), A_367) | k4_xboole_0(A_367, B_368)=C_369)), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.78/2.73  tff(c_6240, plain, (![B_373, C_374]: (~r2_hidden('#skF_3'(k1_relat_1('#skF_11'), B_373, C_374), B_373) | r2_hidden('#skF_4'(k1_relat_1('#skF_11'), B_373, C_374), B_373) | k4_xboole_0(k1_relat_1('#skF_11'), B_373)=C_374 | ~r2_hidden('#skF_4'(k1_relat_1('#skF_11'), B_373, C_374), '#skF_10'))), inference(resolution, [status(thm)], [c_611, c_6126])).
% 7.78/2.73  tff(c_6255, plain, (~r2_hidden('#skF_3'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11')) | r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11')) | k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'))='#skF_10' | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_2791, c_6240])).
% 7.78/2.73  tff(c_6271, plain, (~r2_hidden('#skF_3'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11')) | r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11')) | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_294, c_6255])).
% 7.78/2.73  tff(c_6272, plain, (~r2_hidden('#skF_3'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11')) | r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_86, c_86, c_6271])).
% 7.78/2.73  tff(c_6759, plain, (~r2_hidden('#skF_3'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_6272])).
% 7.78/2.73  tff(c_6762, plain, (r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), '#skF_10') | k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'))='#skF_10'), inference(resolution, [status(thm)], [c_36, c_6759])).
% 7.78/2.73  tff(c_6767, plain, (r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), '#skF_10') | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_294, c_6762])).
% 7.78/2.73  tff(c_6768, plain, (r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_86, c_6767])).
% 7.78/2.73  tff(c_342, plain, (![B_95, A_96]: (r1_xboole_0(k1_relat_1(B_95), A_96) | k9_relat_1(B_95, A_96)!=k1_xboole_0 | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.78/2.73  tff(c_38, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.78/2.73  tff(c_1089, plain, (![B_148, A_149]: (k3_xboole_0(k1_relat_1(B_148), A_149)=k1_xboole_0 | k9_relat_1(B_148, A_149)!=k1_xboole_0 | ~v1_relat_1(B_148))), inference(resolution, [status(thm)], [c_342, c_38])).
% 7.78/2.73  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.78/2.73  tff(c_1109, plain, (![D_6, A_149, B_148]: (r2_hidden(D_6, k1_xboole_0) | ~r2_hidden(D_6, A_149) | ~r2_hidden(D_6, k1_relat_1(B_148)) | k9_relat_1(B_148, A_149)!=k1_xboole_0 | ~v1_relat_1(B_148))), inference(superposition, [status(thm), theory('equality')], [c_1089, c_2])).
% 7.78/2.73  tff(c_1125, plain, (![D_6, A_149, B_148]: (~r2_hidden(D_6, A_149) | ~r2_hidden(D_6, k1_relat_1(B_148)) | k9_relat_1(B_148, A_149)!=k1_xboole_0 | ~v1_relat_1(B_148))), inference(negUnitSimplification, [status(thm)], [c_119, c_1109])).
% 7.78/2.73  tff(c_8528, plain, (![B_426]: (~r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1(B_426)) | k9_relat_1(B_426, '#skF_10')!=k1_xboole_0 | ~v1_relat_1(B_426))), inference(resolution, [status(thm)], [c_6768, c_1125])).
% 7.78/2.73  tff(c_8532, plain, (k9_relat_1('#skF_11', '#skF_10')!=k1_xboole_0 | ~v1_relat_1('#skF_11') | ~r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), '#skF_10')), inference(resolution, [status(thm)], [c_611, c_8528])).
% 7.78/2.73  tff(c_8539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6768, c_88, c_82, c_8532])).
% 7.78/2.73  tff(c_8540, plain, (r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_6272])).
% 7.78/2.73  tff(c_8541, plain, (r2_hidden('#skF_3'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_6272])).
% 7.78/2.73  tff(c_8570, plain, (r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), '#skF_10') | k4_xboole_0(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'))='#skF_10'), inference(resolution, [status(thm)], [c_8541, c_34])).
% 7.78/2.73  tff(c_8578, plain, (r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), '#skF_10') | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_294, c_8570])).
% 7.78/2.73  tff(c_8579, plain, (r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_86, c_8578])).
% 7.78/2.73  tff(c_10369, plain, (![B_452]: (~r2_hidden('#skF_4'(k1_relat_1('#skF_11'), k1_relat_1('#skF_11'), '#skF_10'), k1_relat_1(B_452)) | k9_relat_1(B_452, '#skF_10')!=k1_xboole_0 | ~v1_relat_1(B_452))), inference(resolution, [status(thm)], [c_8579, c_1125])).
% 7.78/2.73  tff(c_10372, plain, (k9_relat_1('#skF_11', '#skF_10')!=k1_xboole_0 | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_8540, c_10369])).
% 7.78/2.73  tff(c_10383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_10372])).
% 7.78/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.78/2.73  
% 7.78/2.73  Inference rules
% 7.78/2.73  ----------------------
% 7.78/2.73  #Ref     : 1
% 7.78/2.73  #Sup     : 2247
% 7.78/2.73  #Fact    : 0
% 7.78/2.73  #Define  : 0
% 7.78/2.73  #Split   : 4
% 7.78/2.73  #Chain   : 0
% 7.78/2.73  #Close   : 0
% 7.78/2.73  
% 7.78/2.73  Ordering : KBO
% 7.78/2.73  
% 7.78/2.73  Simplification rules
% 7.78/2.73  ----------------------
% 7.78/2.73  #Subsume      : 383
% 7.78/2.73  #Demod        : 1055
% 7.78/2.73  #Tautology    : 650
% 7.78/2.73  #SimpNegUnit  : 120
% 7.78/2.73  #BackRed      : 7
% 7.78/2.73  
% 7.78/2.73  #Partial instantiations: 0
% 7.78/2.73  #Strategies tried      : 1
% 7.78/2.73  
% 7.78/2.73  Timing (in seconds)
% 7.78/2.73  ----------------------
% 7.78/2.73  Preprocessing        : 0.34
% 7.78/2.73  Parsing              : 0.17
% 7.78/2.73  CNF conversion       : 0.03
% 7.78/2.73  Main loop            : 1.63
% 7.78/2.73  Inferencing          : 0.53
% 7.78/2.73  Reduction            : 0.48
% 7.78/2.73  Demodulation         : 0.32
% 7.78/2.73  BG Simplification    : 0.07
% 7.78/2.73  Subsumption          : 0.42
% 7.78/2.73  Abstraction          : 0.08
% 7.78/2.73  MUC search           : 0.00
% 7.78/2.73  Cooper               : 0.00
% 7.78/2.73  Total                : 2.01
% 7.78/2.73  Index Insertion      : 0.00
% 7.78/2.73  Index Deletion       : 0.00
% 7.78/2.73  Index Matching       : 0.00
% 7.78/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
