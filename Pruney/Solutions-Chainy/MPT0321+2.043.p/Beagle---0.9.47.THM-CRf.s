%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:19 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 434 expanded)
%              Number of leaves         :   30 ( 150 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 ( 988 expanded)
%              Number of equality atoms :   64 ( 502 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_68,plain,
    ( '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_76,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_2'(A_11,B_12),B_12)
      | ~ r2_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_316,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( r2_hidden(k4_tarski(A_120,B_121),k2_zfmisc_1(C_122,D_123))
      | ~ r2_hidden(B_121,D_123)
      | ~ r2_hidden(A_120,C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_161,plain,(
    ! [A_77,C_78,B_79,D_80] :
      ( r2_hidden(A_77,C_78)
      | ~ r2_hidden(k4_tarski(A_77,B_79),k2_zfmisc_1(C_78,D_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_164,plain,(
    ! [A_77,B_79] :
      ( r2_hidden(A_77,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_77,B_79),k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_161])).

tff(c_342,plain,(
    ! [A_120,B_121] :
      ( r2_hidden(A_120,'#skF_11')
      | ~ r2_hidden(B_121,'#skF_10')
      | ~ r2_hidden(A_120,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_316,c_164])).

tff(c_348,plain,(
    ! [B_124] : ~ r2_hidden(B_124,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_365,plain,(
    ! [B_126] : r1_tarski('#skF_10',B_126) ),
    inference(resolution,[status(thm)],[c_6,c_348])).

tff(c_30,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_184,plain,(
    ! [A_93,C_94,B_95] :
      ( ~ r2_hidden(A_93,C_94)
      | ~ r2_hidden(A_93,B_95)
      | ~ r2_hidden(A_93,k5_xboole_0(B_95,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_198,plain,(
    ! [A_96,A_97] :
      ( ~ r2_hidden(A_96,k1_xboole_0)
      | ~ r2_hidden(A_96,A_97)
      | ~ r2_hidden(A_96,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_184])).

tff(c_207,plain,(
    ! [A_98,A_99] :
      ( ~ r2_hidden('#skF_2'(A_98,k1_xboole_0),A_99)
      | ~ r2_xboole_0(A_98,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_198])).

tff(c_214,plain,(
    ! [A_102] : ~ r2_xboole_0(A_102,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_207])).

tff(c_219,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_214])).

tff(c_369,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_365,c_219])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_369])).

tff(c_375,plain,(
    ! [A_127] :
      ( r2_hidden(A_127,'#skF_11')
      | ~ r2_hidden(A_127,'#skF_9') ) ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12),A_11)
      | ~ r2_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_425,plain,(
    ! [B_131] :
      ( ~ r2_xboole_0('#skF_11',B_131)
      | ~ r2_hidden('#skF_2'('#skF_11',B_131),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_375,c_26])).

tff(c_430,plain,(
    ~ r2_xboole_0('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_425])).

tff(c_433,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_8,c_430])).

tff(c_436,plain,(
    ~ r1_tarski('#skF_11','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_433])).

tff(c_437,plain,(
    ! [A_132,B_133] :
      ( r2_hidden(k4_tarski(A_132,B_133),k2_zfmisc_1('#skF_9','#skF_10'))
      | ~ r2_hidden(B_133,'#skF_12')
      | ~ r2_hidden(A_132,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_316])).

tff(c_60,plain,(
    ! [A_49,C_51,B_50,D_52] :
      ( r2_hidden(A_49,C_51)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_455,plain,(
    ! [A_132,B_133] :
      ( r2_hidden(A_132,'#skF_9')
      | ~ r2_hidden(B_133,'#skF_12')
      | ~ r2_hidden(A_132,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_437,c_60])).

tff(c_567,plain,(
    ! [B_143] : ~ r2_hidden(B_143,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_611,plain,(
    ! [B_147] : r1_tarski('#skF_12',B_147) ),
    inference(resolution,[status(thm)],[c_6,c_567])).

tff(c_616,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_611,c_219])).

tff(c_64,plain,(
    ! [A_53] : k2_zfmisc_1(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_674,plain,(
    ! [A_53] : k2_zfmisc_1(A_53,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_616,c_64])).

tff(c_764,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_74])).

tff(c_114,plain,(
    ! [B_63,A_64] :
      ( k1_xboole_0 = B_63
      | k1_xboole_0 = A_64
      | k2_zfmisc_1(A_64,B_63) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_12'
    | k1_xboole_0 = '#skF_11'
    | k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_114])).

tff(c_153,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_671,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_153])).

tff(c_826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_671])).

tff(c_1069,plain,(
    ! [A_174] :
      ( r2_hidden(A_174,'#skF_9')
      | ~ r2_hidden(A_174,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_1102,plain,(
    ! [B_175] :
      ( r2_hidden('#skF_1'('#skF_11',B_175),'#skF_9')
      | r1_tarski('#skF_11',B_175) ) ),
    inference(resolution,[status(thm)],[c_6,c_1069])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1112,plain,(
    r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_1102,c_4])).

tff(c_1119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_436,c_1112])).

tff(c_1120,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_1122,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_1120])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1135,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_72])).

tff(c_1134,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_70])).

tff(c_1121,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_1140,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_1121])).

tff(c_62,plain,(
    ! [B_54,A_53] :
      ( k1_xboole_0 = B_54
      | k1_xboole_0 = A_53
      | k2_zfmisc_1(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1178,plain,(
    ! [B_182,A_183] :
      ( B_182 = '#skF_12'
      | A_183 = '#skF_12'
      | k2_zfmisc_1(A_183,B_182) != '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_1122,c_1122,c_62])).

tff(c_1187,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_1178])).

tff(c_1195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1135,c_1134,c_1187])).

tff(c_1196,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_1120])).

tff(c_1209,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_70])).

tff(c_1216,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_1121])).

tff(c_1254,plain,(
    ! [B_190,A_191] :
      ( B_190 = '#skF_11'
      | A_191 = '#skF_11'
      | k2_zfmisc_1(A_191,B_190) != '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_1196,c_1196,c_62])).

tff(c_1263,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1216,c_1254])).

tff(c_1271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1209,c_1263])).

tff(c_1272,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1532,plain,(
    ! [A_254,B_255,C_256,D_257] :
      ( r2_hidden(k4_tarski(A_254,B_255),k2_zfmisc_1(C_256,D_257))
      | ~ r2_hidden(B_255,D_257)
      | ~ r2_hidden(A_254,C_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1273,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_1300,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_9','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1273,c_74])).

tff(c_1375,plain,(
    ! [B_222,D_223,A_224,C_225] :
      ( r2_hidden(B_222,D_223)
      | ~ r2_hidden(k4_tarski(A_224,B_222),k2_zfmisc_1(C_225,D_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1378,plain,(
    ! [B_222,A_224] :
      ( r2_hidden(B_222,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_224,B_222),k2_zfmisc_1('#skF_9','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_1375])).

tff(c_1554,plain,(
    ! [B_255,A_254] :
      ( r2_hidden(B_255,'#skF_10')
      | ~ r2_hidden(B_255,'#skF_12')
      | ~ r2_hidden(A_254,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1532,c_1378])).

tff(c_1559,plain,(
    ! [A_258] : ~ r2_hidden(A_258,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1554])).

tff(c_1576,plain,(
    ! [B_260] : r1_tarski('#skF_9',B_260) ),
    inference(resolution,[status(thm)],[c_6,c_1559])).

tff(c_1422,plain,(
    ! [A_237,C_238,B_239] :
      ( ~ r2_hidden(A_237,C_238)
      | ~ r2_hidden(A_237,B_239)
      | ~ r2_hidden(A_237,k5_xboole_0(B_239,C_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1440,plain,(
    ! [A_240,A_241] :
      ( ~ r2_hidden(A_240,k1_xboole_0)
      | ~ r2_hidden(A_240,A_241)
      | ~ r2_hidden(A_240,A_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1422])).

tff(c_1449,plain,(
    ! [A_242,A_243] :
      ( ~ r2_hidden('#skF_2'(A_242,k1_xboole_0),A_243)
      | ~ r2_xboole_0(A_242,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_1440])).

tff(c_1460,plain,(
    ! [A_244] : ~ r2_xboole_0(A_244,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_1449])).

tff(c_1465,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1460])).

tff(c_1580,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1576,c_1465])).

tff(c_1584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1580])).

tff(c_1586,plain,(
    ! [B_261] :
      ( r2_hidden(B_261,'#skF_10')
      | ~ r2_hidden(B_261,'#skF_12') ) ),
    inference(splitRight,[status(thm)],[c_1554])).

tff(c_1664,plain,(
    ! [A_268] :
      ( r1_tarski(A_268,'#skF_10')
      | ~ r2_hidden('#skF_1'(A_268,'#skF_10'),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_1586,c_4])).

tff(c_1669,plain,(
    r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_6,c_1664])).

tff(c_1648,plain,(
    ! [A_266,B_267] :
      ( r2_hidden(k4_tarski(A_266,B_267),k2_zfmisc_1('#skF_9','#skF_12'))
      | ~ r2_hidden(B_267,'#skF_10')
      | ~ r2_hidden(A_266,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_1532])).

tff(c_58,plain,(
    ! [B_50,D_52,A_49,C_51] :
      ( r2_hidden(B_50,D_52)
      | ~ r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1661,plain,(
    ! [B_267,A_266] :
      ( r2_hidden(B_267,'#skF_12')
      | ~ r2_hidden(B_267,'#skF_10')
      | ~ r2_hidden(A_266,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1648,c_58])).

tff(c_1671,plain,(
    ! [A_269] : ~ r2_hidden(A_269,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1661])).

tff(c_1734,plain,(
    ! [B_274] : r1_tarski('#skF_9',B_274) ),
    inference(resolution,[status(thm)],[c_6,c_1671])).

tff(c_1738,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1734,c_1465])).

tff(c_1742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1738])).

tff(c_1744,plain,(
    ! [B_275] :
      ( r2_hidden(B_275,'#skF_12')
      | ~ r2_hidden(B_275,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_1661])).

tff(c_1764,plain,(
    ! [A_276] :
      ( r2_hidden('#skF_2'(A_276,'#skF_10'),'#skF_12')
      | ~ r2_xboole_0(A_276,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_28,c_1744])).

tff(c_1777,plain,(
    ~ r2_xboole_0('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_1764,c_26])).

tff(c_1784,plain,
    ( '#skF_10' = '#skF_12'
    | ~ r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_8,c_1777])).

tff(c_1787,plain,(
    '#skF_10' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1669,c_1784])).

tff(c_1789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1272,c_1787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:00:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.69  
% 3.62/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.69  %$ r2_xboole_0 > r2_hidden > r1_tarski > k5_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1 > #skF_12
% 3.62/1.69  
% 3.62/1.69  %Foreground sorts:
% 3.62/1.69  
% 3.62/1.69  
% 3.62/1.69  %Background operators:
% 3.62/1.69  
% 3.62/1.69  
% 3.62/1.69  %Foreground operators:
% 3.62/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.69  tff('#skF_11', type, '#skF_11': $i).
% 3.62/1.69  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.62/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.62/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.69  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.62/1.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.62/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.69  tff('#skF_10', type, '#skF_10': $i).
% 3.62/1.69  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.62/1.69  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.62/1.69  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.62/1.69  tff('#skF_9', type, '#skF_9': $i).
% 3.62/1.69  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.62/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.62/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.62/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.62/1.69  tff('#skF_12', type, '#skF_12': $i).
% 3.62/1.69  
% 3.62/1.71  tff(f_93, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 3.62/1.71  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.62/1.71  tff(f_56, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.62/1.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.62/1.71  tff(f_76, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.62/1.71  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.62/1.71  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.62/1.71  tff(f_82, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.62/1.71  tff(c_68, plain, ('#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.62/1.71  tff(c_76, plain, ('#skF_11'!='#skF_9'), inference(splitLeft, [status(thm)], [c_68])).
% 3.62/1.71  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.62/1.71  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_2'(A_11, B_12), B_12) | ~r2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.62/1.71  tff(c_70, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.62/1.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.62/1.71  tff(c_316, plain, (![A_120, B_121, C_122, D_123]: (r2_hidden(k4_tarski(A_120, B_121), k2_zfmisc_1(C_122, D_123)) | ~r2_hidden(B_121, D_123) | ~r2_hidden(A_120, C_122))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.62/1.71  tff(c_74, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.62/1.71  tff(c_161, plain, (![A_77, C_78, B_79, D_80]: (r2_hidden(A_77, C_78) | ~r2_hidden(k4_tarski(A_77, B_79), k2_zfmisc_1(C_78, D_80)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.62/1.71  tff(c_164, plain, (![A_77, B_79]: (r2_hidden(A_77, '#skF_11') | ~r2_hidden(k4_tarski(A_77, B_79), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_161])).
% 3.62/1.71  tff(c_342, plain, (![A_120, B_121]: (r2_hidden(A_120, '#skF_11') | ~r2_hidden(B_121, '#skF_10') | ~r2_hidden(A_120, '#skF_9'))), inference(resolution, [status(thm)], [c_316, c_164])).
% 3.62/1.71  tff(c_348, plain, (![B_124]: (~r2_hidden(B_124, '#skF_10'))), inference(splitLeft, [status(thm)], [c_342])).
% 3.62/1.71  tff(c_365, plain, (![B_126]: (r1_tarski('#skF_10', B_126))), inference(resolution, [status(thm)], [c_6, c_348])).
% 3.62/1.71  tff(c_30, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.62/1.71  tff(c_184, plain, (![A_93, C_94, B_95]: (~r2_hidden(A_93, C_94) | ~r2_hidden(A_93, B_95) | ~r2_hidden(A_93, k5_xboole_0(B_95, C_94)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.71  tff(c_198, plain, (![A_96, A_97]: (~r2_hidden(A_96, k1_xboole_0) | ~r2_hidden(A_96, A_97) | ~r2_hidden(A_96, A_97))), inference(superposition, [status(thm), theory('equality')], [c_30, c_184])).
% 3.62/1.71  tff(c_207, plain, (![A_98, A_99]: (~r2_hidden('#skF_2'(A_98, k1_xboole_0), A_99) | ~r2_xboole_0(A_98, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_198])).
% 3.62/1.71  tff(c_214, plain, (![A_102]: (~r2_xboole_0(A_102, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_207])).
% 3.62/1.71  tff(c_219, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_214])).
% 3.62/1.71  tff(c_369, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_365, c_219])).
% 3.62/1.71  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_369])).
% 3.62/1.71  tff(c_375, plain, (![A_127]: (r2_hidden(A_127, '#skF_11') | ~r2_hidden(A_127, '#skF_9'))), inference(splitRight, [status(thm)], [c_342])).
% 3.62/1.71  tff(c_26, plain, (![A_11, B_12]: (~r2_hidden('#skF_2'(A_11, B_12), A_11) | ~r2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.62/1.71  tff(c_425, plain, (![B_131]: (~r2_xboole_0('#skF_11', B_131) | ~r2_hidden('#skF_2'('#skF_11', B_131), '#skF_9'))), inference(resolution, [status(thm)], [c_375, c_26])).
% 3.62/1.71  tff(c_430, plain, (~r2_xboole_0('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_28, c_425])).
% 3.62/1.71  tff(c_433, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_8, c_430])).
% 3.62/1.71  tff(c_436, plain, (~r1_tarski('#skF_11', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_76, c_433])).
% 3.62/1.71  tff(c_437, plain, (![A_132, B_133]: (r2_hidden(k4_tarski(A_132, B_133), k2_zfmisc_1('#skF_9', '#skF_10')) | ~r2_hidden(B_133, '#skF_12') | ~r2_hidden(A_132, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_316])).
% 3.62/1.71  tff(c_60, plain, (![A_49, C_51, B_50, D_52]: (r2_hidden(A_49, C_51) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.62/1.71  tff(c_455, plain, (![A_132, B_133]: (r2_hidden(A_132, '#skF_9') | ~r2_hidden(B_133, '#skF_12') | ~r2_hidden(A_132, '#skF_11'))), inference(resolution, [status(thm)], [c_437, c_60])).
% 3.62/1.71  tff(c_567, plain, (![B_143]: (~r2_hidden(B_143, '#skF_12'))), inference(splitLeft, [status(thm)], [c_455])).
% 3.62/1.71  tff(c_611, plain, (![B_147]: (r1_tarski('#skF_12', B_147))), inference(resolution, [status(thm)], [c_6, c_567])).
% 3.62/1.71  tff(c_616, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_611, c_219])).
% 3.62/1.71  tff(c_64, plain, (![A_53]: (k2_zfmisc_1(A_53, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.62/1.71  tff(c_674, plain, (![A_53]: (k2_zfmisc_1(A_53, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_616, c_64])).
% 3.62/1.71  tff(c_764, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_674, c_74])).
% 3.62/1.71  tff(c_114, plain, (![B_63, A_64]: (k1_xboole_0=B_63 | k1_xboole_0=A_64 | k2_zfmisc_1(A_64, B_63)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.62/1.71  tff(c_117, plain, (k1_xboole_0='#skF_12' | k1_xboole_0='#skF_11' | k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_74, c_114])).
% 3.62/1.71  tff(c_153, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_117])).
% 3.62/1.71  tff(c_671, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_153])).
% 3.62/1.71  tff(c_826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_764, c_671])).
% 3.62/1.71  tff(c_1069, plain, (![A_174]: (r2_hidden(A_174, '#skF_9') | ~r2_hidden(A_174, '#skF_11'))), inference(splitRight, [status(thm)], [c_455])).
% 3.62/1.71  tff(c_1102, plain, (![B_175]: (r2_hidden('#skF_1'('#skF_11', B_175), '#skF_9') | r1_tarski('#skF_11', B_175))), inference(resolution, [status(thm)], [c_6, c_1069])).
% 3.62/1.71  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.62/1.71  tff(c_1112, plain, (r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_1102, c_4])).
% 3.62/1.71  tff(c_1119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_436, c_436, c_1112])).
% 3.62/1.71  tff(c_1120, plain, (k1_xboole_0='#skF_11' | k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_117])).
% 3.62/1.71  tff(c_1122, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_1120])).
% 3.62/1.71  tff(c_72, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.62/1.71  tff(c_1135, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_72])).
% 3.62/1.71  tff(c_1134, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_70])).
% 3.62/1.71  tff(c_1121, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_117])).
% 3.62/1.71  tff(c_1140, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_1121])).
% 3.62/1.71  tff(c_62, plain, (![B_54, A_53]: (k1_xboole_0=B_54 | k1_xboole_0=A_53 | k2_zfmisc_1(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.62/1.71  tff(c_1178, plain, (![B_182, A_183]: (B_182='#skF_12' | A_183='#skF_12' | k2_zfmisc_1(A_183, B_182)!='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_1122, c_1122, c_62])).
% 3.62/1.71  tff(c_1187, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_1140, c_1178])).
% 3.62/1.71  tff(c_1195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1135, c_1134, c_1187])).
% 3.62/1.71  tff(c_1196, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_1120])).
% 3.62/1.71  tff(c_1209, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_70])).
% 3.62/1.71  tff(c_1216, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_1121])).
% 3.62/1.71  tff(c_1254, plain, (![B_190, A_191]: (B_190='#skF_11' | A_191='#skF_11' | k2_zfmisc_1(A_191, B_190)!='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1196, c_1196, c_1196, c_62])).
% 3.62/1.71  tff(c_1263, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_1216, c_1254])).
% 3.62/1.71  tff(c_1271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_1209, c_1263])).
% 3.62/1.71  tff(c_1272, plain, ('#skF_10'!='#skF_12'), inference(splitRight, [status(thm)], [c_68])).
% 3.62/1.71  tff(c_1532, plain, (![A_254, B_255, C_256, D_257]: (r2_hidden(k4_tarski(A_254, B_255), k2_zfmisc_1(C_256, D_257)) | ~r2_hidden(B_255, D_257) | ~r2_hidden(A_254, C_256))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.62/1.71  tff(c_1273, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_68])).
% 3.62/1.71  tff(c_1300, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1273, c_74])).
% 3.62/1.71  tff(c_1375, plain, (![B_222, D_223, A_224, C_225]: (r2_hidden(B_222, D_223) | ~r2_hidden(k4_tarski(A_224, B_222), k2_zfmisc_1(C_225, D_223)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.62/1.71  tff(c_1378, plain, (![B_222, A_224]: (r2_hidden(B_222, '#skF_10') | ~r2_hidden(k4_tarski(A_224, B_222), k2_zfmisc_1('#skF_9', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_1300, c_1375])).
% 3.62/1.71  tff(c_1554, plain, (![B_255, A_254]: (r2_hidden(B_255, '#skF_10') | ~r2_hidden(B_255, '#skF_12') | ~r2_hidden(A_254, '#skF_9'))), inference(resolution, [status(thm)], [c_1532, c_1378])).
% 3.62/1.71  tff(c_1559, plain, (![A_258]: (~r2_hidden(A_258, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1554])).
% 3.62/1.71  tff(c_1576, plain, (![B_260]: (r1_tarski('#skF_9', B_260))), inference(resolution, [status(thm)], [c_6, c_1559])).
% 3.62/1.71  tff(c_1422, plain, (![A_237, C_238, B_239]: (~r2_hidden(A_237, C_238) | ~r2_hidden(A_237, B_239) | ~r2_hidden(A_237, k5_xboole_0(B_239, C_238)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.62/1.71  tff(c_1440, plain, (![A_240, A_241]: (~r2_hidden(A_240, k1_xboole_0) | ~r2_hidden(A_240, A_241) | ~r2_hidden(A_240, A_241))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1422])).
% 3.62/1.71  tff(c_1449, plain, (![A_242, A_243]: (~r2_hidden('#skF_2'(A_242, k1_xboole_0), A_243) | ~r2_xboole_0(A_242, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_1440])).
% 3.62/1.71  tff(c_1460, plain, (![A_244]: (~r2_xboole_0(A_244, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_1449])).
% 3.62/1.71  tff(c_1465, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1460])).
% 3.62/1.71  tff(c_1580, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1576, c_1465])).
% 3.62/1.71  tff(c_1584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1580])).
% 3.62/1.71  tff(c_1586, plain, (![B_261]: (r2_hidden(B_261, '#skF_10') | ~r2_hidden(B_261, '#skF_12'))), inference(splitRight, [status(thm)], [c_1554])).
% 3.62/1.71  tff(c_1664, plain, (![A_268]: (r1_tarski(A_268, '#skF_10') | ~r2_hidden('#skF_1'(A_268, '#skF_10'), '#skF_12'))), inference(resolution, [status(thm)], [c_1586, c_4])).
% 3.62/1.71  tff(c_1669, plain, (r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_6, c_1664])).
% 3.62/1.71  tff(c_1648, plain, (![A_266, B_267]: (r2_hidden(k4_tarski(A_266, B_267), k2_zfmisc_1('#skF_9', '#skF_12')) | ~r2_hidden(B_267, '#skF_10') | ~r2_hidden(A_266, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1300, c_1532])).
% 3.62/1.71  tff(c_58, plain, (![B_50, D_52, A_49, C_51]: (r2_hidden(B_50, D_52) | ~r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.62/1.71  tff(c_1661, plain, (![B_267, A_266]: (r2_hidden(B_267, '#skF_12') | ~r2_hidden(B_267, '#skF_10') | ~r2_hidden(A_266, '#skF_9'))), inference(resolution, [status(thm)], [c_1648, c_58])).
% 3.62/1.71  tff(c_1671, plain, (![A_269]: (~r2_hidden(A_269, '#skF_9'))), inference(splitLeft, [status(thm)], [c_1661])).
% 3.62/1.71  tff(c_1734, plain, (![B_274]: (r1_tarski('#skF_9', B_274))), inference(resolution, [status(thm)], [c_6, c_1671])).
% 3.62/1.71  tff(c_1738, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1734, c_1465])).
% 3.62/1.71  tff(c_1742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1738])).
% 3.62/1.71  tff(c_1744, plain, (![B_275]: (r2_hidden(B_275, '#skF_12') | ~r2_hidden(B_275, '#skF_10'))), inference(splitRight, [status(thm)], [c_1661])).
% 3.62/1.71  tff(c_1764, plain, (![A_276]: (r2_hidden('#skF_2'(A_276, '#skF_10'), '#skF_12') | ~r2_xboole_0(A_276, '#skF_10'))), inference(resolution, [status(thm)], [c_28, c_1744])).
% 3.62/1.71  tff(c_1777, plain, (~r2_xboole_0('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_1764, c_26])).
% 3.62/1.71  tff(c_1784, plain, ('#skF_10'='#skF_12' | ~r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_8, c_1777])).
% 3.62/1.71  tff(c_1787, plain, ('#skF_10'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1669, c_1784])).
% 3.62/1.71  tff(c_1789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1272, c_1787])).
% 3.62/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.71  
% 3.62/1.71  Inference rules
% 3.62/1.71  ----------------------
% 3.62/1.71  #Ref     : 0
% 3.62/1.71  #Sup     : 359
% 3.62/1.71  #Fact    : 0
% 3.62/1.71  #Define  : 0
% 3.62/1.71  #Split   : 10
% 3.62/1.71  #Chain   : 0
% 3.62/1.71  #Close   : 0
% 3.62/1.71  
% 3.62/1.71  Ordering : KBO
% 3.62/1.71  
% 3.62/1.71  Simplification rules
% 3.62/1.71  ----------------------
% 3.62/1.71  #Subsume      : 61
% 3.62/1.71  #Demod        : 125
% 3.62/1.71  #Tautology    : 119
% 3.62/1.71  #SimpNegUnit  : 30
% 3.62/1.71  #BackRed      : 44
% 3.62/1.71  
% 3.62/1.71  #Partial instantiations: 0
% 3.62/1.71  #Strategies tried      : 1
% 3.62/1.71  
% 3.62/1.71  Timing (in seconds)
% 3.62/1.71  ----------------------
% 3.62/1.71  Preprocessing        : 0.32
% 3.62/1.71  Parsing              : 0.16
% 3.62/1.71  CNF conversion       : 0.03
% 3.62/1.71  Main loop            : 0.62
% 3.62/1.72  Inferencing          : 0.22
% 3.62/1.72  Reduction            : 0.18
% 3.62/1.72  Demodulation         : 0.12
% 3.62/1.72  BG Simplification    : 0.03
% 3.62/1.72  Subsumption          : 0.13
% 3.62/1.72  Abstraction          : 0.02
% 3.62/1.72  MUC search           : 0.00
% 3.62/1.72  Cooper               : 0.00
% 3.62/1.72  Total                : 0.98
% 3.62/1.72  Index Insertion      : 0.00
% 3.62/1.72  Index Deletion       : 0.00
% 3.62/1.72  Index Matching       : 0.00
% 3.62/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
