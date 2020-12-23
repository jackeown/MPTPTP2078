%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:13 EST 2020

% Result     : Theorem 14.87s
% Output     : CNFRefutation 15.08s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 583 expanded)
%              Number of leaves         :   39 ( 210 expanded)
%              Depth                    :   14
%              Number of atoms          :  210 (1165 expanded)
%              Number of equality atoms :   88 ( 696 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_104,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_66,plain,
    ( '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_75,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_64,plain,(
    ! [A_66,C_68,B_67,D_69] : k3_xboole_0(k2_zfmisc_1(A_66,C_68),k2_zfmisc_1(B_67,D_69)) = k2_zfmisc_1(k3_xboole_0(A_66,B_67),k3_xboole_0(C_68,D_69)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3085,plain,(
    ! [C_216,A_217,B_218] : k2_xboole_0(k2_zfmisc_1(C_216,A_217),k2_zfmisc_1(C_216,B_218)) = k2_zfmisc_1(C_216,k2_xboole_0(A_217,B_218)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5628,plain,(
    ! [A_309] : k2_xboole_0(k2_zfmisc_1('#skF_11',A_309),k2_zfmisc_1('#skF_9','#skF_10')) = k2_zfmisc_1('#skF_11',k2_xboole_0(A_309,'#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_3085])).

tff(c_30,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_197,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_215,plain,(
    ! [A_24,B_25] : k3_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = A_24 ),
    inference(resolution,[status(thm)],[c_30,c_197])).

tff(c_32311,plain,(
    ! [A_902] : k3_xboole_0(k2_zfmisc_1('#skF_11',A_902),k2_zfmisc_1('#skF_11',k2_xboole_0(A_902,'#skF_12'))) = k2_zfmisc_1('#skF_11',A_902) ),
    inference(superposition,[status(thm),theory(equality)],[c_5628,c_215])).

tff(c_32623,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',k2_xboole_0('#skF_12','#skF_12'))) = k2_zfmisc_1('#skF_11','#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_32311])).

tff(c_32688,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),k3_xboole_0('#skF_12','#skF_10')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64,c_10,c_72,c_32623])).

tff(c_3858,plain,(
    ! [A_239,C_240,B_241,D_242] : k3_xboole_0(k2_zfmisc_1(A_239,C_240),k2_zfmisc_1(B_241,D_242)) = k2_zfmisc_1(k3_xboole_0(A_239,B_241),k3_xboole_0(C_240,D_242)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_15870,plain,(
    ! [B_562,D_563,A_564,C_565] : k3_xboole_0(k2_zfmisc_1(B_562,D_563),k2_zfmisc_1(A_564,C_565)) = k2_zfmisc_1(k3_xboole_0(A_564,B_562),k3_xboole_0(C_565,D_563)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3858,c_4])).

tff(c_26,plain,(
    ! [A_20,B_21] : r1_tarski(k3_xboole_0(A_20,B_21),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16004,plain,(
    ! [A_564,B_562,C_565,D_563] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_564,B_562),k3_xboole_0(C_565,D_563)),k2_zfmisc_1(B_562,D_563)) ),
    inference(superposition,[status(thm),theory(equality)],[c_15870,c_26])).

tff(c_32965,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32688,c_16004])).

tff(c_58,plain,(
    ! [B_61,A_60,C_62] :
      ( ~ r1_tarski(k2_zfmisc_1(B_61,A_60),k2_zfmisc_1(C_62,A_60))
      | r1_tarski(B_61,C_62)
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_33368,plain,
    ( r1_tarski('#skF_9','#skF_11')
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_32965,c_58])).

tff(c_33392,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_33368])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_33399,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_33392,c_18])).

tff(c_33408,plain,(
    ~ r1_tarski('#skF_11','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_33399])).

tff(c_145,plain,(
    ! [B_81,A_82] : k2_xboole_0(B_81,A_82) = k2_xboole_0(A_82,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_160,plain,(
    ! [A_82,B_81] : r1_tarski(A_82,k2_xboole_0(B_81,A_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_30])).

tff(c_213,plain,(
    ! [A_82,B_81] : k3_xboole_0(A_82,k2_xboole_0(B_81,A_82)) = A_82 ),
    inference(resolution,[status(thm)],[c_160,c_197])).

tff(c_744,plain,(
    ! [B_128,A_129,C_130] :
      ( ~ r1_tarski(k2_zfmisc_1(B_128,A_129),k2_zfmisc_1(C_130,A_129))
      | r1_tarski(B_128,C_130)
      | k1_xboole_0 = A_129 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_750,plain,(
    ! [B_128] :
      ( ~ r1_tarski(k2_zfmisc_1(B_128,'#skF_12'),k2_zfmisc_1('#skF_9','#skF_10'))
      | r1_tarski(B_128,'#skF_11')
      | k1_xboole_0 = '#skF_12' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_744])).

tff(c_1178,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_1188,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_68])).

tff(c_16,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_2'(A_14),A_14)
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1187,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_2'(A_14),A_14)
      | A_14 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_16])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1189,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_70])).

tff(c_32,plain,(
    ! [E_58,F_59,A_26,B_27] :
      ( r2_hidden(k4_tarski(E_58,F_59),k2_zfmisc_1(A_26,B_27))
      | ~ r2_hidden(F_59,B_27)
      | ~ r2_hidden(E_58,A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [B_17] : r1_tarski(B_17,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_217,plain,(
    ! [B_17] : k3_xboole_0(B_17,B_17) = B_17 ),
    inference(resolution,[status(thm)],[c_22,c_197])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_576,plain,(
    ! [A_108,B_109,C_110] :
      ( ~ r1_xboole_0(A_108,B_109)
      | ~ r2_hidden(C_110,k3_xboole_0(A_108,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_597,plain,(
    ! [B_111,C_112] :
      ( ~ r1_xboole_0(B_111,B_111)
      | ~ r2_hidden(C_112,B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_576])).

tff(c_600,plain,(
    ! [C_112,B_6] :
      ( ~ r2_hidden(C_112,B_6)
      | k3_xboole_0(B_6,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_597])).

tff(c_602,plain,(
    ! [C_112,B_6] :
      ( ~ r2_hidden(C_112,B_6)
      | k1_xboole_0 != B_6 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_600])).

tff(c_1194,plain,(
    ! [C_112] : ~ r2_hidden(C_112,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_602])).

tff(c_2238,plain,(
    ! [A_194,B_195,D_196] :
      ( r2_hidden('#skF_8'(A_194,B_195,k2_zfmisc_1(A_194,B_195),D_196),B_195)
      | ~ r2_hidden(D_196,k2_zfmisc_1(A_194,B_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2259,plain,(
    ! [D_196] :
      ( r2_hidden('#skF_8'('#skF_11','#skF_12',k2_zfmisc_1('#skF_9','#skF_10'),D_196),'#skF_12')
      | ~ r2_hidden(D_196,k2_zfmisc_1('#skF_11','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2238])).

tff(c_2264,plain,(
    ! [D_196] :
      ( r2_hidden('#skF_8'('#skF_11','#skF_12',k2_zfmisc_1('#skF_9','#skF_10'),D_196),'#skF_12')
      | ~ r2_hidden(D_196,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2259])).

tff(c_2290,plain,(
    ! [D_198] : ~ r2_hidden(D_198,k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_1194,c_2264])).

tff(c_2316,plain,(
    ! [F_59,E_58] :
      ( ~ r2_hidden(F_59,'#skF_10')
      | ~ r2_hidden(E_58,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_2290])).

tff(c_2484,plain,(
    ! [E_202] : ~ r2_hidden(E_202,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2316])).

tff(c_2496,plain,(
    '#skF_9' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1187,c_2484])).

tff(c_2506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1189,c_2496])).

tff(c_2508,plain,(
    ! [F_203] : ~ r2_hidden(F_203,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_2316])).

tff(c_2520,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_1187,c_2508])).

tff(c_2530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1188,c_2520])).

tff(c_2532,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_960,plain,(
    ! [A_139,B_140,C_141] :
      ( ~ r1_tarski(k2_zfmisc_1(A_139,B_140),k2_zfmisc_1(A_139,C_141))
      | r1_tarski(B_140,C_141)
      | k1_xboole_0 = A_139 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_966,plain,(
    ! [B_140] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_11',B_140),k2_zfmisc_1('#skF_9','#skF_10'))
      | r1_tarski(B_140,'#skF_12')
      | k1_xboole_0 = '#skF_11' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_960])).

tff(c_4137,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_966])).

tff(c_4148,plain,(
    '#skF_11' != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_68])).

tff(c_4147,plain,(
    ! [A_14] :
      ( r2_hidden('#skF_2'(A_14),A_14)
      | A_14 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_16])).

tff(c_4154,plain,(
    ! [C_112] : ~ r2_hidden(C_112,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4137,c_602])).

tff(c_4297,plain,(
    ! [A_263,B_264,D_265] :
      ( r2_hidden('#skF_7'(A_263,B_264,k2_zfmisc_1(A_263,B_264),D_265),A_263)
      | ~ r2_hidden(D_265,k2_zfmisc_1(A_263,B_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4311,plain,(
    ! [D_265] :
      ( r2_hidden('#skF_7'('#skF_11','#skF_12',k2_zfmisc_1('#skF_9','#skF_10'),D_265),'#skF_11')
      | ~ r2_hidden(D_265,k2_zfmisc_1('#skF_11','#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4297])).

tff(c_4315,plain,(
    ! [D_265] :
      ( r2_hidden('#skF_7'('#skF_11','#skF_12',k2_zfmisc_1('#skF_9','#skF_10'),D_265),'#skF_11')
      | ~ r2_hidden(D_265,k2_zfmisc_1('#skF_9','#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4311])).

tff(c_4317,plain,(
    ! [D_266] : ~ r2_hidden(D_266,k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_4154,c_4315])).

tff(c_4341,plain,(
    ! [F_59,E_58] :
      ( ~ r2_hidden(F_59,'#skF_10')
      | ~ r2_hidden(E_58,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_4317])).

tff(c_4636,plain,(
    ! [E_277] : ~ r2_hidden(E_277,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4341])).

tff(c_4650,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4147,c_4636])).

tff(c_4664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_4650])).

tff(c_4666,plain,(
    ! [F_278] : ~ r2_hidden(F_278,'#skF_10') ),
    inference(splitRight,[status(thm)],[c_4341])).

tff(c_4674,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_4147,c_4666])).

tff(c_4687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4148,c_4674])).

tff(c_4689,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_966])).

tff(c_963,plain,(
    ! [C_141] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',C_141))
      | r1_tarski('#skF_12',C_141)
      | k1_xboole_0 = '#skF_11' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_960])).

tff(c_5263,plain,(
    ! [C_141] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11',C_141))
      | r1_tarski('#skF_12',C_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4689,c_963])).

tff(c_33389,plain,(
    r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_32965,c_5263])).

tff(c_33419,plain,
    ( '#skF_10' = '#skF_12'
    | ~ r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_33389,c_18])).

tff(c_35977,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitLeft,[status(thm)],[c_33419])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_33421,plain,(
    k3_xboole_0('#skF_12','#skF_10') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_33389,c_28])).

tff(c_33410,plain,(
    k3_xboole_0('#skF_9','#skF_11') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_33392,c_28])).

tff(c_2533,plain,(
    ! [A_204,C_205,B_206] : k2_xboole_0(k2_zfmisc_1(A_204,C_205),k2_zfmisc_1(B_206,C_205)) = k2_zfmisc_1(k2_xboole_0(A_204,B_206),C_205) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2681,plain,(
    ! [A_209] : k2_xboole_0(k2_zfmisc_1(A_209,'#skF_12'),k2_zfmisc_1('#skF_9','#skF_10')) = k2_zfmisc_1(k2_xboole_0(A_209,'#skF_11'),'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2533])).

tff(c_35996,plain,(
    ! [A_911] : k3_xboole_0(k2_zfmisc_1(A_911,'#skF_12'),k2_zfmisc_1(k2_xboole_0(A_911,'#skF_11'),'#skF_12')) = k2_zfmisc_1(A_911,'#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2681,c_215])).

tff(c_36314,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1(k2_xboole_0('#skF_11','#skF_11'),'#skF_12')) = k2_zfmisc_1('#skF_11','#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_35996])).

tff(c_36380,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_9','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33421,c_33410,c_4,c_64,c_10,c_72,c_36314])).

tff(c_56,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_tarski(k2_zfmisc_1(A_60,B_61),k2_zfmisc_1(A_60,C_62))
      | r1_tarski(B_61,C_62)
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36706,plain,(
    ! [C_62] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_12'),k2_zfmisc_1('#skF_9',C_62))
      | r1_tarski('#skF_10',C_62)
      | k1_xboole_0 = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36380,c_56])).

tff(c_39929,plain,(
    ! [C_929] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_12'),k2_zfmisc_1('#skF_9',C_929))
      | r1_tarski('#skF_10',C_929) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_36706])).

tff(c_39986,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_22,c_39929])).

tff(c_39996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35977,c_39986])).

tff(c_39997,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_33419])).

tff(c_263,plain,(
    ! [A_90,B_91] :
      ( k2_xboole_0(A_90,B_91) = B_91
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_282,plain,(
    ! [A_20,B_21] : k2_xboole_0(k3_xboole_0(A_20,B_21),A_20) = A_20 ),
    inference(resolution,[status(thm)],[c_26,c_263])).

tff(c_7121,plain,(
    ! [A_345,C_346,B_347] : r1_tarski(k2_zfmisc_1(A_345,C_346),k2_zfmisc_1(k2_xboole_0(A_345,B_347),C_346)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2533,c_30])).

tff(c_8571,plain,(
    ! [A_394,B_395,C_396] : r1_tarski(k2_zfmisc_1(k3_xboole_0(A_394,B_395),C_396),k2_zfmisc_1(A_394,C_396)) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_7121])).

tff(c_8641,plain,(
    ! [B_395] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_11',B_395),'#skF_12'),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_8571])).

tff(c_43541,plain,(
    ! [B_954] : r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_11',B_954),'#skF_12'),k2_zfmisc_1('#skF_9','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39997,c_8641])).

tff(c_43544,plain,(
    ! [B_954] :
      ( r1_tarski(k3_xboole_0('#skF_11',B_954),'#skF_9')
      | k1_xboole_0 = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_43541,c_58])).

tff(c_43623,plain,(
    ! [B_955] : r1_tarski(k3_xboole_0('#skF_11',B_955),'#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_2532,c_43544])).

tff(c_43653,plain,(
    r1_tarski('#skF_11','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_43623])).

tff(c_43677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33408,c_43653])).

tff(c_43678,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_43679,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_43752,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') = k2_zfmisc_1('#skF_9','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43679,c_72])).

tff(c_45465,plain,(
    ! [A_1049,B_1050,C_1051] :
      ( ~ r1_tarski(k2_zfmisc_1(A_1049,B_1050),k2_zfmisc_1(A_1049,C_1051))
      | r1_tarski(B_1050,C_1051)
      | k1_xboole_0 = A_1049 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_45474,plain,(
    ! [C_1051] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_12'),k2_zfmisc_1('#skF_9',C_1051))
      | r1_tarski('#skF_10',C_1051)
      | k1_xboole_0 = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43752,c_45465])).

tff(c_45634,plain,(
    ! [C_1056] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_12'),k2_zfmisc_1('#skF_9',C_1056))
      | r1_tarski('#skF_10',C_1056) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_45474])).

tff(c_45649,plain,(
    r1_tarski('#skF_10','#skF_12') ),
    inference(resolution,[status(thm)],[c_22,c_45634])).

tff(c_45651,plain,
    ( '#skF_10' = '#skF_12'
    | ~ r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_45649,c_18])).

tff(c_45660,plain,(
    ~ r1_tarski('#skF_12','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_43678,c_45651])).

tff(c_45477,plain,(
    ! [B_1050] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9',B_1050),k2_zfmisc_1('#skF_9','#skF_12'))
      | r1_tarski(B_1050,'#skF_10')
      | k1_xboole_0 = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43752,c_45465])).

tff(c_45918,plain,(
    ! [B_1061] :
      ( ~ r1_tarski(k2_zfmisc_1('#skF_9',B_1061),k2_zfmisc_1('#skF_9','#skF_12'))
      | r1_tarski(B_1061,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_45477])).

tff(c_45925,plain,(
    r1_tarski('#skF_12','#skF_10') ),
    inference(resolution,[status(thm)],[c_22,c_45918])).

tff(c_45931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45660,c_45925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.87/7.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.87/7.53  
% 14.87/7.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.87/7.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 14.87/7.53  
% 14.87/7.53  %Foreground sorts:
% 14.87/7.53  
% 14.87/7.53  
% 14.87/7.53  %Background operators:
% 14.87/7.53  
% 14.87/7.53  
% 14.87/7.53  %Foreground operators:
% 14.87/7.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 14.87/7.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.87/7.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.87/7.53  tff('#skF_11', type, '#skF_11': $i).
% 14.87/7.53  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 14.87/7.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.87/7.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.87/7.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.87/7.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.87/7.53  tff('#skF_10', type, '#skF_10': $i).
% 14.87/7.53  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 14.87/7.53  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 14.87/7.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.87/7.53  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 14.87/7.53  tff('#skF_9', type, '#skF_9': $i).
% 14.87/7.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.87/7.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.87/7.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.87/7.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.87/7.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.87/7.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.87/7.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.87/7.53  tff('#skF_12', type, '#skF_12': $i).
% 14.87/7.53  
% 15.08/7.55  tff(f_115, negated_conjecture, ~(![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 15.08/7.55  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 15.08/7.55  tff(f_104, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 15.08/7.55  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 15.08/7.55  tff(f_102, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 15.08/7.55  tff(f_75, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 15.08/7.55  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.08/7.55  tff(f_69, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.08/7.55  tff(f_98, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 15.08/7.55  tff(f_63, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.08/7.55  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 15.08/7.55  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 15.08/7.55  tff(f_87, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 15.08/7.55  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 15.08/7.55  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 15.08/7.55  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 15.08/7.55  tff(c_66, plain, ('#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_115])).
% 15.08/7.55  tff(c_75, plain, ('#skF_11'!='#skF_9'), inference(splitLeft, [status(thm)], [c_66])).
% 15.08/7.55  tff(c_68, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_115])).
% 15.08/7.55  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.08/7.55  tff(c_64, plain, (![A_66, C_68, B_67, D_69]: (k3_xboole_0(k2_zfmisc_1(A_66, C_68), k2_zfmisc_1(B_67, D_69))=k2_zfmisc_1(k3_xboole_0(A_66, B_67), k3_xboole_0(C_68, D_69)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.08/7.55  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.08/7.55  tff(c_72, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k2_zfmisc_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_115])).
% 15.08/7.55  tff(c_3085, plain, (![C_216, A_217, B_218]: (k2_xboole_0(k2_zfmisc_1(C_216, A_217), k2_zfmisc_1(C_216, B_218))=k2_zfmisc_1(C_216, k2_xboole_0(A_217, B_218)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.08/7.55  tff(c_5628, plain, (![A_309]: (k2_xboole_0(k2_zfmisc_1('#skF_11', A_309), k2_zfmisc_1('#skF_9', '#skF_10'))=k2_zfmisc_1('#skF_11', k2_xboole_0(A_309, '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_3085])).
% 15.08/7.55  tff(c_30, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.08/7.55  tff(c_197, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.08/7.55  tff(c_215, plain, (![A_24, B_25]: (k3_xboole_0(A_24, k2_xboole_0(A_24, B_25))=A_24)), inference(resolution, [status(thm)], [c_30, c_197])).
% 15.08/7.55  tff(c_32311, plain, (![A_902]: (k3_xboole_0(k2_zfmisc_1('#skF_11', A_902), k2_zfmisc_1('#skF_11', k2_xboole_0(A_902, '#skF_12')))=k2_zfmisc_1('#skF_11', A_902))), inference(superposition, [status(thm), theory('equality')], [c_5628, c_215])).
% 15.08/7.55  tff(c_32623, plain, (k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', k2_xboole_0('#skF_12', '#skF_12')))=k2_zfmisc_1('#skF_11', '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_72, c_32311])).
% 15.08/7.55  tff(c_32688, plain, (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), k3_xboole_0('#skF_12', '#skF_10'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64, c_10, c_72, c_32623])).
% 15.08/7.55  tff(c_3858, plain, (![A_239, C_240, B_241, D_242]: (k3_xboole_0(k2_zfmisc_1(A_239, C_240), k2_zfmisc_1(B_241, D_242))=k2_zfmisc_1(k3_xboole_0(A_239, B_241), k3_xboole_0(C_240, D_242)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 15.08/7.55  tff(c_15870, plain, (![B_562, D_563, A_564, C_565]: (k3_xboole_0(k2_zfmisc_1(B_562, D_563), k2_zfmisc_1(A_564, C_565))=k2_zfmisc_1(k3_xboole_0(A_564, B_562), k3_xboole_0(C_565, D_563)))), inference(superposition, [status(thm), theory('equality')], [c_3858, c_4])).
% 15.08/7.55  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(k3_xboole_0(A_20, B_21), A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.08/7.55  tff(c_16004, plain, (![A_564, B_562, C_565, D_563]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_564, B_562), k3_xboole_0(C_565, D_563)), k2_zfmisc_1(B_562, D_563)))), inference(superposition, [status(thm), theory('equality')], [c_15870, c_26])).
% 15.08/7.55  tff(c_32965, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_32688, c_16004])).
% 15.08/7.55  tff(c_58, plain, (![B_61, A_60, C_62]: (~r1_tarski(k2_zfmisc_1(B_61, A_60), k2_zfmisc_1(C_62, A_60)) | r1_tarski(B_61, C_62) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.08/7.55  tff(c_33368, plain, (r1_tarski('#skF_9', '#skF_11') | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_32965, c_58])).
% 15.08/7.55  tff(c_33392, plain, (r1_tarski('#skF_9', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_68, c_33368])).
% 15.08/7.55  tff(c_18, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.08/7.55  tff(c_33399, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_33392, c_18])).
% 15.08/7.55  tff(c_33408, plain, (~r1_tarski('#skF_11', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_75, c_33399])).
% 15.08/7.55  tff(c_145, plain, (![B_81, A_82]: (k2_xboole_0(B_81, A_82)=k2_xboole_0(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.08/7.55  tff(c_160, plain, (![A_82, B_81]: (r1_tarski(A_82, k2_xboole_0(B_81, A_82)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_30])).
% 15.08/7.55  tff(c_213, plain, (![A_82, B_81]: (k3_xboole_0(A_82, k2_xboole_0(B_81, A_82))=A_82)), inference(resolution, [status(thm)], [c_160, c_197])).
% 15.08/7.55  tff(c_744, plain, (![B_128, A_129, C_130]: (~r1_tarski(k2_zfmisc_1(B_128, A_129), k2_zfmisc_1(C_130, A_129)) | r1_tarski(B_128, C_130) | k1_xboole_0=A_129)), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.08/7.55  tff(c_750, plain, (![B_128]: (~r1_tarski(k2_zfmisc_1(B_128, '#skF_12'), k2_zfmisc_1('#skF_9', '#skF_10')) | r1_tarski(B_128, '#skF_11') | k1_xboole_0='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_72, c_744])).
% 15.08/7.55  tff(c_1178, plain, (k1_xboole_0='#skF_12'), inference(splitLeft, [status(thm)], [c_750])).
% 15.08/7.55  tff(c_1188, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_68])).
% 15.08/7.55  tff(c_16, plain, (![A_14]: (r2_hidden('#skF_2'(A_14), A_14) | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.08/7.55  tff(c_1187, plain, (![A_14]: (r2_hidden('#skF_2'(A_14), A_14) | A_14='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_16])).
% 15.08/7.55  tff(c_70, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_115])).
% 15.08/7.55  tff(c_1189, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_70])).
% 15.08/7.55  tff(c_32, plain, (![E_58, F_59, A_26, B_27]: (r2_hidden(k4_tarski(E_58, F_59), k2_zfmisc_1(A_26, B_27)) | ~r2_hidden(F_59, B_27) | ~r2_hidden(E_58, A_26))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.08/7.55  tff(c_22, plain, (![B_17]: (r1_tarski(B_17, B_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.08/7.55  tff(c_217, plain, (![B_17]: (k3_xboole_0(B_17, B_17)=B_17)), inference(resolution, [status(thm)], [c_22, c_197])).
% 15.08/7.55  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.08/7.55  tff(c_576, plain, (![A_108, B_109, C_110]: (~r1_xboole_0(A_108, B_109) | ~r2_hidden(C_110, k3_xboole_0(A_108, B_109)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.08/7.55  tff(c_597, plain, (![B_111, C_112]: (~r1_xboole_0(B_111, B_111) | ~r2_hidden(C_112, B_111))), inference(superposition, [status(thm), theory('equality')], [c_217, c_576])).
% 15.08/7.55  tff(c_600, plain, (![C_112, B_6]: (~r2_hidden(C_112, B_6) | k3_xboole_0(B_6, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_597])).
% 15.08/7.55  tff(c_602, plain, (![C_112, B_6]: (~r2_hidden(C_112, B_6) | k1_xboole_0!=B_6)), inference(demodulation, [status(thm), theory('equality')], [c_217, c_600])).
% 15.08/7.55  tff(c_1194, plain, (![C_112]: (~r2_hidden(C_112, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_602])).
% 15.08/7.55  tff(c_2238, plain, (![A_194, B_195, D_196]: (r2_hidden('#skF_8'(A_194, B_195, k2_zfmisc_1(A_194, B_195), D_196), B_195) | ~r2_hidden(D_196, k2_zfmisc_1(A_194, B_195)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.08/7.55  tff(c_2259, plain, (![D_196]: (r2_hidden('#skF_8'('#skF_11', '#skF_12', k2_zfmisc_1('#skF_9', '#skF_10'), D_196), '#skF_12') | ~r2_hidden(D_196, k2_zfmisc_1('#skF_11', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2238])).
% 15.08/7.55  tff(c_2264, plain, (![D_196]: (r2_hidden('#skF_8'('#skF_11', '#skF_12', k2_zfmisc_1('#skF_9', '#skF_10'), D_196), '#skF_12') | ~r2_hidden(D_196, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2259])).
% 15.08/7.55  tff(c_2290, plain, (![D_198]: (~r2_hidden(D_198, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_1194, c_2264])).
% 15.08/7.55  tff(c_2316, plain, (![F_59, E_58]: (~r2_hidden(F_59, '#skF_10') | ~r2_hidden(E_58, '#skF_9'))), inference(resolution, [status(thm)], [c_32, c_2290])).
% 15.08/7.55  tff(c_2484, plain, (![E_202]: (~r2_hidden(E_202, '#skF_9'))), inference(splitLeft, [status(thm)], [c_2316])).
% 15.08/7.55  tff(c_2496, plain, ('#skF_9'='#skF_12'), inference(resolution, [status(thm)], [c_1187, c_2484])).
% 15.08/7.55  tff(c_2506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1189, c_2496])).
% 15.08/7.55  tff(c_2508, plain, (![F_203]: (~r2_hidden(F_203, '#skF_10'))), inference(splitRight, [status(thm)], [c_2316])).
% 15.08/7.55  tff(c_2520, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_1187, c_2508])).
% 15.08/7.55  tff(c_2530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1188, c_2520])).
% 15.08/7.55  tff(c_2532, plain, (k1_xboole_0!='#skF_12'), inference(splitRight, [status(thm)], [c_750])).
% 15.08/7.55  tff(c_960, plain, (![A_139, B_140, C_141]: (~r1_tarski(k2_zfmisc_1(A_139, B_140), k2_zfmisc_1(A_139, C_141)) | r1_tarski(B_140, C_141) | k1_xboole_0=A_139)), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.08/7.55  tff(c_966, plain, (![B_140]: (~r1_tarski(k2_zfmisc_1('#skF_11', B_140), k2_zfmisc_1('#skF_9', '#skF_10')) | r1_tarski(B_140, '#skF_12') | k1_xboole_0='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_72, c_960])).
% 15.08/7.55  tff(c_4137, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_966])).
% 15.08/7.55  tff(c_4148, plain, ('#skF_11'!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_68])).
% 15.08/7.55  tff(c_4147, plain, (![A_14]: (r2_hidden('#skF_2'(A_14), A_14) | A_14='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_16])).
% 15.08/7.55  tff(c_4154, plain, (![C_112]: (~r2_hidden(C_112, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_4137, c_602])).
% 15.08/7.55  tff(c_4297, plain, (![A_263, B_264, D_265]: (r2_hidden('#skF_7'(A_263, B_264, k2_zfmisc_1(A_263, B_264), D_265), A_263) | ~r2_hidden(D_265, k2_zfmisc_1(A_263, B_264)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 15.08/7.55  tff(c_4311, plain, (![D_265]: (r2_hidden('#skF_7'('#skF_11', '#skF_12', k2_zfmisc_1('#skF_9', '#skF_10'), D_265), '#skF_11') | ~r2_hidden(D_265, k2_zfmisc_1('#skF_11', '#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_4297])).
% 15.08/7.55  tff(c_4315, plain, (![D_265]: (r2_hidden('#skF_7'('#skF_11', '#skF_12', k2_zfmisc_1('#skF_9', '#skF_10'), D_265), '#skF_11') | ~r2_hidden(D_265, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4311])).
% 15.08/7.55  tff(c_4317, plain, (![D_266]: (~r2_hidden(D_266, k2_zfmisc_1('#skF_9', '#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_4154, c_4315])).
% 15.08/7.55  tff(c_4341, plain, (![F_59, E_58]: (~r2_hidden(F_59, '#skF_10') | ~r2_hidden(E_58, '#skF_9'))), inference(resolution, [status(thm)], [c_32, c_4317])).
% 15.08/7.55  tff(c_4636, plain, (![E_277]: (~r2_hidden(E_277, '#skF_9'))), inference(splitLeft, [status(thm)], [c_4341])).
% 15.08/7.55  tff(c_4650, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_4147, c_4636])).
% 15.08/7.55  tff(c_4664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_4650])).
% 15.08/7.55  tff(c_4666, plain, (![F_278]: (~r2_hidden(F_278, '#skF_10'))), inference(splitRight, [status(thm)], [c_4341])).
% 15.08/7.55  tff(c_4674, plain, ('#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_4147, c_4666])).
% 15.08/7.55  tff(c_4687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4148, c_4674])).
% 15.08/7.55  tff(c_4689, plain, (k1_xboole_0!='#skF_11'), inference(splitRight, [status(thm)], [c_966])).
% 15.08/7.55  tff(c_963, plain, (![C_141]: (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', C_141)) | r1_tarski('#skF_12', C_141) | k1_xboole_0='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_72, c_960])).
% 15.08/7.55  tff(c_5263, plain, (![C_141]: (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', C_141)) | r1_tarski('#skF_12', C_141))), inference(negUnitSimplification, [status(thm)], [c_4689, c_963])).
% 15.08/7.55  tff(c_33389, plain, (r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_32965, c_5263])).
% 15.08/7.55  tff(c_33419, plain, ('#skF_10'='#skF_12' | ~r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_33389, c_18])).
% 15.08/7.55  tff(c_35977, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitLeft, [status(thm)], [c_33419])).
% 15.08/7.55  tff(c_28, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.08/7.55  tff(c_33421, plain, (k3_xboole_0('#skF_12', '#skF_10')='#skF_12'), inference(resolution, [status(thm)], [c_33389, c_28])).
% 15.08/7.55  tff(c_33410, plain, (k3_xboole_0('#skF_9', '#skF_11')='#skF_9'), inference(resolution, [status(thm)], [c_33392, c_28])).
% 15.08/7.55  tff(c_2533, plain, (![A_204, C_205, B_206]: (k2_xboole_0(k2_zfmisc_1(A_204, C_205), k2_zfmisc_1(B_206, C_205))=k2_zfmisc_1(k2_xboole_0(A_204, B_206), C_205))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.08/7.55  tff(c_2681, plain, (![A_209]: (k2_xboole_0(k2_zfmisc_1(A_209, '#skF_12'), k2_zfmisc_1('#skF_9', '#skF_10'))=k2_zfmisc_1(k2_xboole_0(A_209, '#skF_11'), '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2533])).
% 15.08/7.55  tff(c_35996, plain, (![A_911]: (k3_xboole_0(k2_zfmisc_1(A_911, '#skF_12'), k2_zfmisc_1(k2_xboole_0(A_911, '#skF_11'), '#skF_12'))=k2_zfmisc_1(A_911, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_2681, c_215])).
% 15.08/7.55  tff(c_36314, plain, (k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1(k2_xboole_0('#skF_11', '#skF_11'), '#skF_12'))=k2_zfmisc_1('#skF_11', '#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_72, c_35996])).
% 15.08/7.55  tff(c_36380, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_33421, c_33410, c_4, c_64, c_10, c_72, c_36314])).
% 15.08/7.55  tff(c_56, plain, (![A_60, B_61, C_62]: (~r1_tarski(k2_zfmisc_1(A_60, B_61), k2_zfmisc_1(A_60, C_62)) | r1_tarski(B_61, C_62) | k1_xboole_0=A_60)), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.08/7.55  tff(c_36706, plain, (![C_62]: (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_12'), k2_zfmisc_1('#skF_9', C_62)) | r1_tarski('#skF_10', C_62) | k1_xboole_0='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_36380, c_56])).
% 15.08/7.55  tff(c_39929, plain, (![C_929]: (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_12'), k2_zfmisc_1('#skF_9', C_929)) | r1_tarski('#skF_10', C_929))), inference(negUnitSimplification, [status(thm)], [c_70, c_36706])).
% 15.08/7.55  tff(c_39986, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_22, c_39929])).
% 15.08/7.55  tff(c_39996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35977, c_39986])).
% 15.08/7.55  tff(c_39997, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_33419])).
% 15.08/7.55  tff(c_263, plain, (![A_90, B_91]: (k2_xboole_0(A_90, B_91)=B_91 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.08/7.55  tff(c_282, plain, (![A_20, B_21]: (k2_xboole_0(k3_xboole_0(A_20, B_21), A_20)=A_20)), inference(resolution, [status(thm)], [c_26, c_263])).
% 15.08/7.55  tff(c_7121, plain, (![A_345, C_346, B_347]: (r1_tarski(k2_zfmisc_1(A_345, C_346), k2_zfmisc_1(k2_xboole_0(A_345, B_347), C_346)))), inference(superposition, [status(thm), theory('equality')], [c_2533, c_30])).
% 15.08/7.55  tff(c_8571, plain, (![A_394, B_395, C_396]: (r1_tarski(k2_zfmisc_1(k3_xboole_0(A_394, B_395), C_396), k2_zfmisc_1(A_394, C_396)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_7121])).
% 15.08/7.55  tff(c_8641, plain, (![B_395]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_11', B_395), '#skF_12'), k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_8571])).
% 15.08/7.55  tff(c_43541, plain, (![B_954]: (r1_tarski(k2_zfmisc_1(k3_xboole_0('#skF_11', B_954), '#skF_12'), k2_zfmisc_1('#skF_9', '#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_39997, c_8641])).
% 15.08/7.55  tff(c_43544, plain, (![B_954]: (r1_tarski(k3_xboole_0('#skF_11', B_954), '#skF_9') | k1_xboole_0='#skF_12')), inference(resolution, [status(thm)], [c_43541, c_58])).
% 15.08/7.55  tff(c_43623, plain, (![B_955]: (r1_tarski(k3_xboole_0('#skF_11', B_955), '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_2532, c_43544])).
% 15.08/7.55  tff(c_43653, plain, (r1_tarski('#skF_11', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_213, c_43623])).
% 15.08/7.55  tff(c_43677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33408, c_43653])).
% 15.08/7.55  tff(c_43678, plain, ('#skF_10'!='#skF_12'), inference(splitRight, [status(thm)], [c_66])).
% 15.08/7.55  tff(c_43679, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_66])).
% 15.08/7.55  tff(c_43752, plain, (k2_zfmisc_1('#skF_9', '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_43679, c_72])).
% 15.08/7.55  tff(c_45465, plain, (![A_1049, B_1050, C_1051]: (~r1_tarski(k2_zfmisc_1(A_1049, B_1050), k2_zfmisc_1(A_1049, C_1051)) | r1_tarski(B_1050, C_1051) | k1_xboole_0=A_1049)), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.08/7.55  tff(c_45474, plain, (![C_1051]: (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_12'), k2_zfmisc_1('#skF_9', C_1051)) | r1_tarski('#skF_10', C_1051) | k1_xboole_0='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_43752, c_45465])).
% 15.08/7.55  tff(c_45634, plain, (![C_1056]: (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_12'), k2_zfmisc_1('#skF_9', C_1056)) | r1_tarski('#skF_10', C_1056))), inference(negUnitSimplification, [status(thm)], [c_70, c_45474])).
% 15.08/7.55  tff(c_45649, plain, (r1_tarski('#skF_10', '#skF_12')), inference(resolution, [status(thm)], [c_22, c_45634])).
% 15.08/7.55  tff(c_45651, plain, ('#skF_10'='#skF_12' | ~r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_45649, c_18])).
% 15.08/7.55  tff(c_45660, plain, (~r1_tarski('#skF_12', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_43678, c_45651])).
% 15.08/7.55  tff(c_45477, plain, (![B_1050]: (~r1_tarski(k2_zfmisc_1('#skF_9', B_1050), k2_zfmisc_1('#skF_9', '#skF_12')) | r1_tarski(B_1050, '#skF_10') | k1_xboole_0='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_43752, c_45465])).
% 15.08/7.55  tff(c_45918, plain, (![B_1061]: (~r1_tarski(k2_zfmisc_1('#skF_9', B_1061), k2_zfmisc_1('#skF_9', '#skF_12')) | r1_tarski(B_1061, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_70, c_45477])).
% 15.08/7.55  tff(c_45925, plain, (r1_tarski('#skF_12', '#skF_10')), inference(resolution, [status(thm)], [c_22, c_45918])).
% 15.08/7.55  tff(c_45931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45660, c_45925])).
% 15.08/7.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.08/7.55  
% 15.08/7.55  Inference rules
% 15.08/7.55  ----------------------
% 15.08/7.55  #Ref     : 5
% 15.08/7.55  #Sup     : 12642
% 15.08/7.55  #Fact    : 0
% 15.08/7.55  #Define  : 0
% 15.08/7.55  #Split   : 16
% 15.08/7.55  #Chain   : 0
% 15.08/7.55  #Close   : 0
% 15.08/7.55  
% 15.08/7.55  Ordering : KBO
% 15.08/7.55  
% 15.08/7.55  Simplification rules
% 15.08/7.55  ----------------------
% 15.08/7.55  #Subsume      : 3786
% 15.08/7.55  #Demod        : 7713
% 15.08/7.55  #Tautology    : 3701
% 15.08/7.55  #SimpNegUnit  : 221
% 15.08/7.55  #BackRed      : 117
% 15.08/7.55  
% 15.08/7.55  #Partial instantiations: 0
% 15.08/7.55  #Strategies tried      : 1
% 15.08/7.55  
% 15.08/7.55  Timing (in seconds)
% 15.08/7.55  ----------------------
% 15.08/7.56  Preprocessing        : 0.33
% 15.08/7.56  Parsing              : 0.17
% 15.08/7.56  CNF conversion       : 0.03
% 15.08/7.56  Main loop            : 6.44
% 15.08/7.56  Inferencing          : 1.00
% 15.08/7.56  Reduction            : 3.45
% 15.08/7.56  Demodulation         : 2.93
% 15.08/7.56  BG Simplification    : 0.13
% 15.08/7.56  Subsumption          : 1.51
% 15.08/7.56  Abstraction          : 0.18
% 15.08/7.56  MUC search           : 0.00
% 15.08/7.56  Cooper               : 0.00
% 15.08/7.56  Total                : 6.82
% 15.08/7.56  Index Insertion      : 0.00
% 15.08/7.56  Index Deletion       : 0.00
% 15.08/7.56  Index Matching       : 0.00
% 15.08/7.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
