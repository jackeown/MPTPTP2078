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
% DateTime   : Thu Dec  3 09:50:16 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 315 expanded)
%              Number of leaves         :   38 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          :  170 ( 755 expanded)
%              Number of equality atoms :   80 ( 592 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_92,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_147,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_28,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_96,plain,(
    k2_xboole_0('#skF_8','#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_480,plain,(
    ! [D_132,A_133,B_134] :
      ( ~ r2_hidden(D_132,A_133)
      | r2_hidden(D_132,k2_xboole_0(A_133,B_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_490,plain,(
    ! [D_135] :
      ( ~ r2_hidden(D_135,'#skF_8')
      | r2_hidden(D_135,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_480])).

tff(c_52,plain,(
    ! [C_37,A_33] :
      ( C_37 = A_33
      | ~ r2_hidden(C_37,k1_tarski(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_495,plain,(
    ! [D_136] :
      ( D_136 = '#skF_7'
      | ~ r2_hidden(D_136,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_490,c_52])).

tff(c_503,plain,
    ( '#skF_4'('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_28,c_495])).

tff(c_507,plain,(
    '#skF_4'('#skF_8') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_503])).

tff(c_511,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_28])).

tff(c_514,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_511])).

tff(c_82,plain,(
    ! [A_74,B_75] :
      ( r1_tarski(k1_tarski(A_74),B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_90,plain,
    ( k1_xboole_0 != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_148,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_139,plain,(
    ! [A_85,B_86] : r1_tarski(A_85,k2_xboole_0(A_85,B_86)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_142,plain,(
    r1_tarski('#skF_8',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_139])).

tff(c_535,plain,(
    ! [B_140,A_141] :
      ( B_140 = A_141
      | ~ r1_tarski(B_140,A_141)
      | ~ r1_tarski(A_141,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_543,plain,
    ( k1_tarski('#skF_7') = '#skF_8'
    | ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_142,c_535])).

tff(c_553,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_543])).

tff(c_561,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_553])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_561])).

tff(c_567,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_94,plain,
    ( k1_tarski('#skF_7') != '#skF_9'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_579,plain,(
    '#skF_9' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_567,c_94])).

tff(c_569,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_96])).

tff(c_566,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_811,plain,(
    ! [D_168,B_169,A_170] :
      ( ~ r2_hidden(D_168,B_169)
      | r2_hidden(D_168,k2_xboole_0(A_170,B_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_823,plain,(
    ! [D_171] :
      ( ~ r2_hidden(D_171,'#skF_9')
      | r2_hidden(D_171,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_569,c_811])).

tff(c_831,plain,
    ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
    | k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_28,c_823])).

tff(c_836,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_831])).

tff(c_597,plain,(
    ! [C_143,A_144] :
      ( C_143 = A_144
      | ~ r2_hidden(C_143,k1_tarski(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_600,plain,(
    ! [C_143] :
      ( C_143 = '#skF_7'
      | ~ r2_hidden(C_143,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_597])).

tff(c_849,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_836,c_600])).

tff(c_855,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | k1_xboole_0 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_28])).

tff(c_858,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_566,c_855])).

tff(c_652,plain,(
    ! [A_151,B_152] :
      ( r1_tarski(k1_tarski(A_151),B_152)
      | ~ r2_hidden(A_151,B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_658,plain,(
    ! [B_152] :
      ( r1_tarski('#skF_8',B_152)
      | ~ r2_hidden('#skF_7',B_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_652])).

tff(c_868,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_858,c_658])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_871,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_868,c_38])).

tff(c_873,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_871])).

tff(c_875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_579,c_873])).

tff(c_876,plain,(
    k1_tarski('#skF_7') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_877,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_910,plain,
    ( '#skF_9' != '#skF_8'
    | k1_tarski('#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_90])).

tff(c_911,plain,(
    k1_tarski('#skF_7') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_910])).

tff(c_26,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_935,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | A_14 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_28])).

tff(c_1049,plain,(
    ! [D_199,B_200,A_201] :
      ( ~ r2_hidden(D_199,B_200)
      | r2_hidden(D_199,k2_xboole_0(A_201,B_200)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1059,plain,(
    ! [D_202] :
      ( ~ r2_hidden(D_202,'#skF_9')
      | r2_hidden(D_202,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1049])).

tff(c_1064,plain,(
    ! [D_203] :
      ( D_203 = '#skF_7'
      | ~ r2_hidden(D_203,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1059,c_52])).

tff(c_1069,plain,
    ( '#skF_4'('#skF_9') = '#skF_7'
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_935,c_1064])).

tff(c_1080,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1069])).

tff(c_1084,plain,(
    k2_xboole_0('#skF_8','#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_96])).

tff(c_1085,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1084])).

tff(c_1087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_911,c_1085])).

tff(c_1089,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1069])).

tff(c_1088,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1069])).

tff(c_1098,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_935])).

tff(c_1101,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1089,c_1098])).

tff(c_1133,plain,(
    ! [A_211,B_212] :
      ( r2_hidden('#skF_1'(A_211,B_212),A_211)
      | r1_tarski(A_211,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1070,plain,(
    ! [D_204,A_205,B_206] :
      ( ~ r2_hidden(D_204,A_205)
      | r2_hidden(D_204,k2_xboole_0(A_205,B_206)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1090,plain,(
    ! [D_207] :
      ( ~ r2_hidden(D_207,'#skF_8')
      | r2_hidden(D_207,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1070])).

tff(c_1094,plain,(
    ! [D_207] :
      ( D_207 = '#skF_7'
      | ~ r2_hidden(D_207,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1090,c_52])).

tff(c_1153,plain,(
    ! [B_213] :
      ( '#skF_1'('#skF_8',B_213) = '#skF_7'
      | r1_tarski('#skF_8',B_213) ) ),
    inference(resolution,[status(thm)],[c_1133,c_1094])).

tff(c_1339,plain,(
    ! [B_223] :
      ( k2_xboole_0('#skF_8',B_223) = B_223
      | '#skF_1'('#skF_8',B_223) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1153,c_38])).

tff(c_1367,plain,
    ( k1_tarski('#skF_7') = '#skF_9'
    | '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_96])).

tff(c_1394,plain,(
    '#skF_1'('#skF_8','#skF_9') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_876,c_1367])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1420,plain,
    ( ~ r2_hidden('#skF_7','#skF_9')
    | r1_tarski('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_4])).

tff(c_1427,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_1420])).

tff(c_1438,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1427,c_38])).

tff(c_1445,plain,(
    k1_tarski('#skF_7') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1438,c_96])).

tff(c_1447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_876,c_1445])).

tff(c_1448,plain,(
    '#skF_9' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_910])).

tff(c_1449,plain,(
    k1_tarski('#skF_7') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_910])).

tff(c_1452,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1449,c_96])).

tff(c_1490,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_4'(A_14),A_14)
      | A_14 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_28])).

tff(c_1686,plain,(
    ! [D_252,B_253,A_254] :
      ( ~ r2_hidden(D_252,B_253)
      | r2_hidden(D_252,k2_xboole_0(A_254,B_253)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1698,plain,(
    ! [D_255] :
      ( ~ r2_hidden(D_255,'#skF_9')
      | r2_hidden(D_255,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1452,c_1686])).

tff(c_1706,plain,
    ( r2_hidden('#skF_4'('#skF_9'),'#skF_8')
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1490,c_1698])).

tff(c_1711,plain,(
    r2_hidden('#skF_4'('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1448,c_1706])).

tff(c_1492,plain,(
    ! [C_230,A_231] :
      ( C_230 = A_231
      | ~ r2_hidden(C_230,k1_tarski(A_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1499,plain,(
    ! [C_230] :
      ( C_230 = '#skF_7'
      | ~ r2_hidden(C_230,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_1492])).

tff(c_1715,plain,(
    '#skF_4'('#skF_9') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1711,c_1499])).

tff(c_1721,plain,
    ( r2_hidden('#skF_7','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_1715,c_1490])).

tff(c_1724,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1448,c_1721])).

tff(c_1557,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(k1_tarski(A_238),B_239)
      | ~ r2_hidden(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1566,plain,(
    ! [B_239] :
      ( r1_tarski('#skF_8',B_239)
      | ~ r2_hidden('#skF_7',B_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_1557])).

tff(c_1734,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_1724,c_1566])).

tff(c_1737,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1734,c_38])).

tff(c_1739,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_1737])).

tff(c_1741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1448,c_1739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.53  
% 3.28/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.53  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 3.28/1.53  
% 3.28/1.53  %Foreground sorts:
% 3.28/1.53  
% 3.28/1.53  
% 3.28/1.53  %Background operators:
% 3.28/1.53  
% 3.28/1.53  
% 3.28/1.53  %Foreground operators:
% 3.28/1.53  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.28/1.53  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.28/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.28/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.28/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.53  tff('#skF_9', type, '#skF_9': $i).
% 3.28/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.28/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.28/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.28/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.28/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.53  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.28/1.53  
% 3.28/1.55  tff(f_130, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.28/1.55  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.28/1.55  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.28/1.55  tff(f_84, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.28/1.55  tff(f_104, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.28/1.55  tff(f_71, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.28/1.55  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.55  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.28/1.55  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.28/1.55  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.28/1.55  tff(c_92, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.28/1.55  tff(c_147, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_92])).
% 3.28/1.55  tff(c_28, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.55  tff(c_96, plain, (k2_xboole_0('#skF_8', '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.28/1.55  tff(c_480, plain, (![D_132, A_133, B_134]: (~r2_hidden(D_132, A_133) | r2_hidden(D_132, k2_xboole_0(A_133, B_134)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.55  tff(c_490, plain, (![D_135]: (~r2_hidden(D_135, '#skF_8') | r2_hidden(D_135, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_480])).
% 3.28/1.55  tff(c_52, plain, (![C_37, A_33]: (C_37=A_33 | ~r2_hidden(C_37, k1_tarski(A_33)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.55  tff(c_495, plain, (![D_136]: (D_136='#skF_7' | ~r2_hidden(D_136, '#skF_8'))), inference(resolution, [status(thm)], [c_490, c_52])).
% 3.28/1.55  tff(c_503, plain, ('#skF_4'('#skF_8')='#skF_7' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_28, c_495])).
% 3.28/1.55  tff(c_507, plain, ('#skF_4'('#skF_8')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_147, c_503])).
% 3.28/1.55  tff(c_511, plain, (r2_hidden('#skF_7', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_507, c_28])).
% 3.28/1.55  tff(c_514, plain, (r2_hidden('#skF_7', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_147, c_511])).
% 3.28/1.55  tff(c_82, plain, (![A_74, B_75]: (r1_tarski(k1_tarski(A_74), B_75) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.28/1.55  tff(c_90, plain, (k1_xboole_0!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.28/1.55  tff(c_148, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_90])).
% 3.28/1.55  tff(c_139, plain, (![A_85, B_86]: (r1_tarski(A_85, k2_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.55  tff(c_142, plain, (r1_tarski('#skF_8', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_139])).
% 3.28/1.55  tff(c_535, plain, (![B_140, A_141]: (B_140=A_141 | ~r1_tarski(B_140, A_141) | ~r1_tarski(A_141, B_140))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.28/1.55  tff(c_543, plain, (k1_tarski('#skF_7')='#skF_8' | ~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(resolution, [status(thm)], [c_142, c_535])).
% 3.28/1.55  tff(c_553, plain, (~r1_tarski(k1_tarski('#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_148, c_543])).
% 3.28/1.55  tff(c_561, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_82, c_553])).
% 3.28/1.55  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_561])).
% 3.28/1.55  tff(c_567, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_90])).
% 3.28/1.55  tff(c_94, plain, (k1_tarski('#skF_7')!='#skF_9' | k1_tarski('#skF_7')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.28/1.55  tff(c_579, plain, ('#skF_9'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_567, c_567, c_94])).
% 3.28/1.55  tff(c_569, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_567, c_96])).
% 3.28/1.55  tff(c_566, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_90])).
% 3.28/1.55  tff(c_811, plain, (![D_168, B_169, A_170]: (~r2_hidden(D_168, B_169) | r2_hidden(D_168, k2_xboole_0(A_170, B_169)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.55  tff(c_823, plain, (![D_171]: (~r2_hidden(D_171, '#skF_9') | r2_hidden(D_171, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_569, c_811])).
% 3.28/1.55  tff(c_831, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_28, c_823])).
% 3.28/1.55  tff(c_836, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_566, c_831])).
% 3.28/1.55  tff(c_597, plain, (![C_143, A_144]: (C_143=A_144 | ~r2_hidden(C_143, k1_tarski(A_144)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.55  tff(c_600, plain, (![C_143]: (C_143='#skF_7' | ~r2_hidden(C_143, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_567, c_597])).
% 3.28/1.55  tff(c_849, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_836, c_600])).
% 3.28/1.55  tff(c_855, plain, (r2_hidden('#skF_7', '#skF_9') | k1_xboole_0='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_849, c_28])).
% 3.28/1.55  tff(c_858, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_566, c_855])).
% 3.28/1.55  tff(c_652, plain, (![A_151, B_152]: (r1_tarski(k1_tarski(A_151), B_152) | ~r2_hidden(A_151, B_152))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.28/1.55  tff(c_658, plain, (![B_152]: (r1_tarski('#skF_8', B_152) | ~r2_hidden('#skF_7', B_152))), inference(superposition, [status(thm), theory('equality')], [c_567, c_652])).
% 3.28/1.55  tff(c_868, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_858, c_658])).
% 3.28/1.55  tff(c_38, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.28/1.55  tff(c_871, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_868, c_38])).
% 3.28/1.55  tff(c_873, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_569, c_871])).
% 3.28/1.55  tff(c_875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_579, c_873])).
% 3.28/1.55  tff(c_876, plain, (k1_tarski('#skF_7')!='#skF_9'), inference(splitRight, [status(thm)], [c_92])).
% 3.28/1.55  tff(c_877, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_92])).
% 3.28/1.55  tff(c_910, plain, ('#skF_9'!='#skF_8' | k1_tarski('#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_877, c_90])).
% 3.28/1.55  tff(c_911, plain, (k1_tarski('#skF_7')!='#skF_8'), inference(splitLeft, [status(thm)], [c_910])).
% 3.28/1.55  tff(c_26, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.55  tff(c_935, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | A_14='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_877, c_28])).
% 3.28/1.55  tff(c_1049, plain, (![D_199, B_200, A_201]: (~r2_hidden(D_199, B_200) | r2_hidden(D_199, k2_xboole_0(A_201, B_200)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.55  tff(c_1059, plain, (![D_202]: (~r2_hidden(D_202, '#skF_9') | r2_hidden(D_202, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1049])).
% 3.28/1.55  tff(c_1064, plain, (![D_203]: (D_203='#skF_7' | ~r2_hidden(D_203, '#skF_9'))), inference(resolution, [status(thm)], [c_1059, c_52])).
% 3.28/1.55  tff(c_1069, plain, ('#skF_4'('#skF_9')='#skF_7' | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_935, c_1064])).
% 3.28/1.55  tff(c_1080, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_1069])).
% 3.28/1.55  tff(c_1084, plain, (k2_xboole_0('#skF_8', '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_96])).
% 3.28/1.55  tff(c_1085, plain, (k1_tarski('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1084])).
% 3.28/1.55  tff(c_1087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_911, c_1085])).
% 3.28/1.55  tff(c_1089, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_1069])).
% 3.28/1.55  tff(c_1088, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(splitRight, [status(thm)], [c_1069])).
% 3.28/1.55  tff(c_1098, plain, (r2_hidden('#skF_7', '#skF_9') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1088, c_935])).
% 3.28/1.55  tff(c_1101, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1089, c_1098])).
% 3.28/1.55  tff(c_1133, plain, (![A_211, B_212]: (r2_hidden('#skF_1'(A_211, B_212), A_211) | r1_tarski(A_211, B_212))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.28/1.55  tff(c_1070, plain, (![D_204, A_205, B_206]: (~r2_hidden(D_204, A_205) | r2_hidden(D_204, k2_xboole_0(A_205, B_206)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.55  tff(c_1090, plain, (![D_207]: (~r2_hidden(D_207, '#skF_8') | r2_hidden(D_207, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1070])).
% 3.28/1.55  tff(c_1094, plain, (![D_207]: (D_207='#skF_7' | ~r2_hidden(D_207, '#skF_8'))), inference(resolution, [status(thm)], [c_1090, c_52])).
% 3.28/1.55  tff(c_1153, plain, (![B_213]: ('#skF_1'('#skF_8', B_213)='#skF_7' | r1_tarski('#skF_8', B_213))), inference(resolution, [status(thm)], [c_1133, c_1094])).
% 3.28/1.55  tff(c_1339, plain, (![B_223]: (k2_xboole_0('#skF_8', B_223)=B_223 | '#skF_1'('#skF_8', B_223)='#skF_7')), inference(resolution, [status(thm)], [c_1153, c_38])).
% 3.28/1.55  tff(c_1367, plain, (k1_tarski('#skF_7')='#skF_9' | '#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1339, c_96])).
% 3.28/1.55  tff(c_1394, plain, ('#skF_1'('#skF_8', '#skF_9')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_876, c_1367])).
% 3.28/1.55  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.28/1.55  tff(c_1420, plain, (~r2_hidden('#skF_7', '#skF_9') | r1_tarski('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1394, c_4])).
% 3.28/1.55  tff(c_1427, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_1420])).
% 3.28/1.55  tff(c_1438, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_1427, c_38])).
% 3.28/1.55  tff(c_1445, plain, (k1_tarski('#skF_7')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1438, c_96])).
% 3.28/1.55  tff(c_1447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_876, c_1445])).
% 3.28/1.55  tff(c_1448, plain, ('#skF_9'!='#skF_8'), inference(splitRight, [status(thm)], [c_910])).
% 3.28/1.55  tff(c_1449, plain, (k1_tarski('#skF_7')='#skF_8'), inference(splitRight, [status(thm)], [c_910])).
% 3.28/1.55  tff(c_1452, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1449, c_96])).
% 3.28/1.55  tff(c_1490, plain, (![A_14]: (r2_hidden('#skF_4'(A_14), A_14) | A_14='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_877, c_28])).
% 3.28/1.55  tff(c_1686, plain, (![D_252, B_253, A_254]: (~r2_hidden(D_252, B_253) | r2_hidden(D_252, k2_xboole_0(A_254, B_253)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.55  tff(c_1698, plain, (![D_255]: (~r2_hidden(D_255, '#skF_9') | r2_hidden(D_255, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1452, c_1686])).
% 3.28/1.55  tff(c_1706, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8') | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_1490, c_1698])).
% 3.28/1.55  tff(c_1711, plain, (r2_hidden('#skF_4'('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1448, c_1706])).
% 3.28/1.55  tff(c_1492, plain, (![C_230, A_231]: (C_230=A_231 | ~r2_hidden(C_230, k1_tarski(A_231)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.55  tff(c_1499, plain, (![C_230]: (C_230='#skF_7' | ~r2_hidden(C_230, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1449, c_1492])).
% 3.28/1.55  tff(c_1715, plain, ('#skF_4'('#skF_9')='#skF_7'), inference(resolution, [status(thm)], [c_1711, c_1499])).
% 3.28/1.55  tff(c_1721, plain, (r2_hidden('#skF_7', '#skF_9') | '#skF_9'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_1715, c_1490])).
% 3.28/1.55  tff(c_1724, plain, (r2_hidden('#skF_7', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1448, c_1721])).
% 3.28/1.55  tff(c_1557, plain, (![A_238, B_239]: (r1_tarski(k1_tarski(A_238), B_239) | ~r2_hidden(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.28/1.55  tff(c_1566, plain, (![B_239]: (r1_tarski('#skF_8', B_239) | ~r2_hidden('#skF_7', B_239))), inference(superposition, [status(thm), theory('equality')], [c_1449, c_1557])).
% 3.28/1.55  tff(c_1734, plain, (r1_tarski('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_1724, c_1566])).
% 3.28/1.55  tff(c_1737, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_1734, c_38])).
% 3.28/1.55  tff(c_1739, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_1737])).
% 3.28/1.55  tff(c_1741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1448, c_1739])).
% 3.28/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.55  
% 3.28/1.55  Inference rules
% 3.28/1.55  ----------------------
% 3.28/1.55  #Ref     : 0
% 3.28/1.55  #Sup     : 364
% 3.28/1.55  #Fact    : 0
% 3.28/1.55  #Define  : 0
% 3.28/1.55  #Split   : 5
% 3.28/1.55  #Chain   : 0
% 3.28/1.55  #Close   : 0
% 3.28/1.55  
% 3.28/1.55  Ordering : KBO
% 3.28/1.55  
% 3.28/1.55  Simplification rules
% 3.28/1.55  ----------------------
% 3.28/1.55  #Subsume      : 24
% 3.28/1.55  #Demod        : 127
% 3.28/1.55  #Tautology    : 231
% 3.28/1.55  #SimpNegUnit  : 30
% 3.28/1.55  #BackRed      : 21
% 3.28/1.55  
% 3.28/1.55  #Partial instantiations: 0
% 3.28/1.55  #Strategies tried      : 1
% 3.28/1.55  
% 3.28/1.55  Timing (in seconds)
% 3.28/1.55  ----------------------
% 3.28/1.56  Preprocessing        : 0.35
% 3.28/1.56  Parsing              : 0.18
% 3.28/1.56  CNF conversion       : 0.03
% 3.28/1.56  Main loop            : 0.44
% 3.28/1.56  Inferencing          : 0.16
% 3.28/1.56  Reduction            : 0.14
% 3.28/1.56  Demodulation         : 0.10
% 3.28/1.56  BG Simplification    : 0.03
% 3.28/1.56  Subsumption          : 0.07
% 3.28/1.56  Abstraction          : 0.02
% 3.28/1.56  MUC search           : 0.00
% 3.28/1.56  Cooper               : 0.00
% 3.28/1.56  Total                : 0.83
% 3.28/1.56  Index Insertion      : 0.00
% 3.28/1.56  Index Deletion       : 0.00
% 3.28/1.56  Index Matching       : 0.00
% 3.28/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
