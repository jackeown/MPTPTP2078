%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:02 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 158 expanded)
%              Number of leaves         :   44 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 179 expanded)
%              Number of equality atoms :   70 ( 117 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_62,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(c_38,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_537,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k3_xboole_0(A_110,B_111)) = k4_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_554,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_537])).

tff(c_557,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_554])).

tff(c_76,plain,(
    ! [B_67] : k4_xboole_0(k1_tarski(B_67),k1_tarski(B_67)) != k1_tarski(B_67) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_558,plain,(
    ! [B_67] : k1_tarski(B_67) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_76])).

tff(c_84,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_232,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_24,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_284,plain,(
    ! [C_82,A_83] :
      ( C_82 = A_83
      | ~ r2_hidden(C_82,k1_tarski(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_292,plain,(
    ! [A_83] :
      ( '#skF_3'(k1_tarski(A_83)) = A_83
      | k1_tarski(A_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_284])).

tff(c_566,plain,(
    ! [A_83] : '#skF_3'(k1_tarski(A_83)) = A_83 ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_292])).

tff(c_30,plain,(
    ! [A_17] : k2_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_354,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_601,plain,(
    ! [A_116,B_117] : k2_xboole_0(A_116,k4_xboole_0(B_117,A_116)) = k2_xboole_0(A_116,B_117) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_630,plain,(
    k2_xboole_0('#skF_9',k1_tarski('#skF_8')) = k2_xboole_0('#skF_9',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_601])).

tff(c_637,plain,(
    k2_xboole_0('#skF_9',k1_tarski('#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_630])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_682,plain,(
    ! [D_119] :
      ( ~ r2_hidden(D_119,k1_tarski('#skF_8'))
      | r2_hidden(D_119,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_6])).

tff(c_686,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_8')),'#skF_9')
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_682])).

tff(c_692,plain,
    ( r2_hidden('#skF_8','#skF_9')
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_686])).

tff(c_694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_232,c_692])).

tff(c_695,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_72,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_306,plain,(
    ! [A_89,B_90] :
      ( k2_xboole_0(A_89,B_90) = B_90
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_310,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(k1_tarski(A_62),B_63) = B_63
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_72,c_306])).

tff(c_26,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k2_xboole_0(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1318,plain,(
    ! [A_157,B_158,C_159] : k5_xboole_0(k5_xboole_0(A_157,B_158),C_159) = k5_xboole_0(A_157,k5_xboole_0(B_158,C_159)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2444,plain,(
    ! [A_214,B_215] : k5_xboole_0(A_214,k5_xboole_0(B_215,k2_xboole_0(A_214,B_215))) = k3_xboole_0(A_214,B_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1318])).

tff(c_185,plain,(
    ! [B_78,A_79] : k5_xboole_0(B_78,A_79) = k5_xboole_0(A_79,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_201,plain,(
    ! [A_79] : k5_xboole_0(k1_xboole_0,A_79) = A_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_34])).

tff(c_1395,plain,(
    ! [A_24,C_159] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_159)) = k5_xboole_0(k1_xboole_0,C_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1318])).

tff(c_1408,plain,(
    ! [A_24,C_159] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_159)) = C_159 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_1395])).

tff(c_2459,plain,(
    ! [B_215,A_214] : k5_xboole_0(B_215,k2_xboole_0(A_214,B_215)) = k5_xboole_0(A_214,k3_xboole_0(A_214,B_215)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2444,c_1408])).

tff(c_2543,plain,(
    ! [B_216,A_217] : k5_xboole_0(B_216,k2_xboole_0(A_217,B_216)) = k4_xboole_0(A_217,B_216) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2459])).

tff(c_2585,plain,(
    ! [B_63,A_62] :
      ( k5_xboole_0(B_63,B_63) = k4_xboole_0(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_2543])).

tff(c_2761,plain,(
    ! [A_222,B_223] :
      ( k4_xboole_0(k1_tarski(A_222),B_223) = k1_xboole_0
      | ~ r2_hidden(A_222,B_223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2585])).

tff(c_696,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_86,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_8'),'#skF_9') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_837,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_696,c_86])).

tff(c_2800,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2761,c_837])).

tff(c_2834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_2800])).

tff(c_2835,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_3472,plain,(
    ! [A_274,B_275,C_276] : k5_xboole_0(k5_xboole_0(A_274,B_275),C_276) = k5_xboole_0(A_274,k5_xboole_0(B_275,C_276)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3536,plain,(
    ! [A_24,C_276] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_276)) = k5_xboole_0(k1_xboole_0,C_276) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_3472])).

tff(c_3550,plain,(
    ! [A_277,C_278] : k5_xboole_0(A_277,k5_xboole_0(A_277,C_278)) = C_278 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_3536])).

tff(c_3593,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3550])).

tff(c_2952,plain,(
    ! [A_238,B_239] :
      ( r1_tarski(k1_tarski(A_238),B_239)
      | ~ r2_hidden(A_238,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2960,plain,(
    ! [A_238,B_239] :
      ( k2_xboole_0(k1_tarski(A_238),B_239) = B_239
      | ~ r2_hidden(A_238,B_239) ) ),
    inference(resolution,[status(thm)],[c_2952,c_28])).

tff(c_3695,plain,(
    ! [A_281,B_282] : k5_xboole_0(k5_xboole_0(A_281,B_282),k2_xboole_0(A_281,B_282)) = k3_xboole_0(A_281,B_282) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3744,plain,(
    ! [A_238,B_239] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_238),B_239),B_239) = k3_xboole_0(k1_tarski(A_238),B_239)
      | ~ r2_hidden(A_238,B_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2960,c_3695])).

tff(c_4628,plain,(
    ! [A_323,B_324] :
      ( k3_xboole_0(k1_tarski(A_323),B_324) = k1_tarski(A_323)
      | ~ r2_hidden(A_323,B_324) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3593,c_2,c_3744])).

tff(c_4651,plain,(
    ! [A_323,B_324] :
      ( k5_xboole_0(k1_tarski(A_323),k1_tarski(A_323)) = k4_xboole_0(k1_tarski(A_323),B_324)
      | ~ r2_hidden(A_323,B_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4628,c_26])).

tff(c_4686,plain,(
    ! [A_325,B_326] :
      ( k4_xboole_0(k1_tarski(A_325),B_326) = k1_xboole_0
      | ~ r2_hidden(A_325,B_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4651])).

tff(c_2836,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_82,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2886,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2836,c_82])).

tff(c_4719,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4686,c_2886])).

tff(c_4748,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2835,c_4719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:52:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.88  
% 4.63/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.89  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 4.63/1.89  
% 4.63/1.89  %Foreground sorts:
% 4.63/1.89  
% 4.63/1.89  
% 4.63/1.89  %Background operators:
% 4.63/1.89  
% 4.63/1.89  
% 4.63/1.89  %Foreground operators:
% 4.63/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.63/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.63/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.63/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.63/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.63/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.63/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.63/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.63/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.63/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.63/1.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.89  tff('#skF_9', type, '#skF_9': $i).
% 4.63/1.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.63/1.89  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.63/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.89  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.63/1.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.63/1.89  
% 4.63/1.90  tff(f_62, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.63/1.90  tff(f_38, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.63/1.90  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.63/1.90  tff(f_98, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.63/1.90  tff(f_105, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 4.63/1.90  tff(f_46, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.63/1.90  tff(f_73, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.63/1.90  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.63/1.90  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.63/1.90  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.63/1.90  tff(f_91, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.63/1.90  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.63/1.90  tff(f_64, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.63/1.90  tff(f_60, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.63/1.90  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.63/1.90  tff(f_58, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.63/1.90  tff(c_38, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.63/1.90  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.63/1.90  tff(c_537, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k3_xboole_0(A_110, B_111))=k4_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.90  tff(c_554, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_537])).
% 4.63/1.90  tff(c_557, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_554])).
% 4.63/1.90  tff(c_76, plain, (![B_67]: (k4_xboole_0(k1_tarski(B_67), k1_tarski(B_67))!=k1_tarski(B_67))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.63/1.90  tff(c_558, plain, (![B_67]: (k1_tarski(B_67)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_557, c_76])).
% 4.63/1.90  tff(c_84, plain, (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.90  tff(c_232, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_84])).
% 4.63/1.90  tff(c_24, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.63/1.90  tff(c_284, plain, (![C_82, A_83]: (C_82=A_83 | ~r2_hidden(C_82, k1_tarski(A_83)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.90  tff(c_292, plain, (![A_83]: ('#skF_3'(k1_tarski(A_83))=A_83 | k1_tarski(A_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_284])).
% 4.63/1.90  tff(c_566, plain, (![A_83]: ('#skF_3'(k1_tarski(A_83))=A_83)), inference(negUnitSimplification, [status(thm)], [c_558, c_292])).
% 4.63/1.90  tff(c_30, plain, (![A_17]: (k2_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.63/1.90  tff(c_88, plain, (r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.90  tff(c_354, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_88])).
% 4.63/1.90  tff(c_601, plain, (![A_116, B_117]: (k2_xboole_0(A_116, k4_xboole_0(B_117, A_116))=k2_xboole_0(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.63/1.90  tff(c_630, plain, (k2_xboole_0('#skF_9', k1_tarski('#skF_8'))=k2_xboole_0('#skF_9', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_354, c_601])).
% 4.63/1.90  tff(c_637, plain, (k2_xboole_0('#skF_9', k1_tarski('#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_630])).
% 4.63/1.90  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.63/1.90  tff(c_682, plain, (![D_119]: (~r2_hidden(D_119, k1_tarski('#skF_8')) | r2_hidden(D_119, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_637, c_6])).
% 4.63/1.90  tff(c_686, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_8')), '#skF_9') | k1_tarski('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_682])).
% 4.63/1.90  tff(c_692, plain, (r2_hidden('#skF_8', '#skF_9') | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_566, c_686])).
% 4.63/1.90  tff(c_694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_558, c_232, c_692])).
% 4.63/1.90  tff(c_695, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_88])).
% 4.63/1.90  tff(c_72, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.90  tff(c_306, plain, (![A_89, B_90]: (k2_xboole_0(A_89, B_90)=B_90 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.90  tff(c_310, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), B_63)=B_63 | ~r2_hidden(A_62, B_63))), inference(resolution, [status(thm)], [c_72, c_306])).
% 4.63/1.90  tff(c_26, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.90  tff(c_40, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k2_xboole_0(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.63/1.90  tff(c_1318, plain, (![A_157, B_158, C_159]: (k5_xboole_0(k5_xboole_0(A_157, B_158), C_159)=k5_xboole_0(A_157, k5_xboole_0(B_158, C_159)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.90  tff(c_2444, plain, (![A_214, B_215]: (k5_xboole_0(A_214, k5_xboole_0(B_215, k2_xboole_0(A_214, B_215)))=k3_xboole_0(A_214, B_215))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1318])).
% 4.63/1.90  tff(c_185, plain, (![B_78, A_79]: (k5_xboole_0(B_78, A_79)=k5_xboole_0(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.63/1.90  tff(c_34, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/1.90  tff(c_201, plain, (![A_79]: (k5_xboole_0(k1_xboole_0, A_79)=A_79)), inference(superposition, [status(thm), theory('equality')], [c_185, c_34])).
% 4.63/1.90  tff(c_1395, plain, (![A_24, C_159]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_159))=k5_xboole_0(k1_xboole_0, C_159))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1318])).
% 4.63/1.90  tff(c_1408, plain, (![A_24, C_159]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_159))=C_159)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_1395])).
% 4.63/1.90  tff(c_2459, plain, (![B_215, A_214]: (k5_xboole_0(B_215, k2_xboole_0(A_214, B_215))=k5_xboole_0(A_214, k3_xboole_0(A_214, B_215)))), inference(superposition, [status(thm), theory('equality')], [c_2444, c_1408])).
% 4.63/1.90  tff(c_2543, plain, (![B_216, A_217]: (k5_xboole_0(B_216, k2_xboole_0(A_217, B_216))=k4_xboole_0(A_217, B_216))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2459])).
% 4.63/1.90  tff(c_2585, plain, (![B_63, A_62]: (k5_xboole_0(B_63, B_63)=k4_xboole_0(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_310, c_2543])).
% 4.63/1.90  tff(c_2761, plain, (![A_222, B_223]: (k4_xboole_0(k1_tarski(A_222), B_223)=k1_xboole_0 | ~r2_hidden(A_222, B_223))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2585])).
% 4.63/1.90  tff(c_696, plain, (k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 4.63/1.90  tff(c_86, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_8'), '#skF_9')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.90  tff(c_837, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_696, c_86])).
% 4.63/1.90  tff(c_2800, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2761, c_837])).
% 4.63/1.90  tff(c_2834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_695, c_2800])).
% 4.63/1.90  tff(c_2835, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 4.63/1.90  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.63/1.90  tff(c_3472, plain, (![A_274, B_275, C_276]: (k5_xboole_0(k5_xboole_0(A_274, B_275), C_276)=k5_xboole_0(A_274, k5_xboole_0(B_275, C_276)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.90  tff(c_3536, plain, (![A_24, C_276]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_276))=k5_xboole_0(k1_xboole_0, C_276))), inference(superposition, [status(thm), theory('equality')], [c_38, c_3472])).
% 4.63/1.90  tff(c_3550, plain, (![A_277, C_278]: (k5_xboole_0(A_277, k5_xboole_0(A_277, C_278))=C_278)), inference(demodulation, [status(thm), theory('equality')], [c_201, c_3536])).
% 4.63/1.90  tff(c_3593, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_3550])).
% 4.63/1.90  tff(c_2952, plain, (![A_238, B_239]: (r1_tarski(k1_tarski(A_238), B_239) | ~r2_hidden(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.90  tff(c_28, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.90  tff(c_2960, plain, (![A_238, B_239]: (k2_xboole_0(k1_tarski(A_238), B_239)=B_239 | ~r2_hidden(A_238, B_239))), inference(resolution, [status(thm)], [c_2952, c_28])).
% 4.63/1.90  tff(c_3695, plain, (![A_281, B_282]: (k5_xboole_0(k5_xboole_0(A_281, B_282), k2_xboole_0(A_281, B_282))=k3_xboole_0(A_281, B_282))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.63/1.90  tff(c_3744, plain, (![A_238, B_239]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_238), B_239), B_239)=k3_xboole_0(k1_tarski(A_238), B_239) | ~r2_hidden(A_238, B_239))), inference(superposition, [status(thm), theory('equality')], [c_2960, c_3695])).
% 4.63/1.90  tff(c_4628, plain, (![A_323, B_324]: (k3_xboole_0(k1_tarski(A_323), B_324)=k1_tarski(A_323) | ~r2_hidden(A_323, B_324))), inference(demodulation, [status(thm), theory('equality')], [c_3593, c_2, c_3744])).
% 4.63/1.90  tff(c_4651, plain, (![A_323, B_324]: (k5_xboole_0(k1_tarski(A_323), k1_tarski(A_323))=k4_xboole_0(k1_tarski(A_323), B_324) | ~r2_hidden(A_323, B_324))), inference(superposition, [status(thm), theory('equality')], [c_4628, c_26])).
% 4.63/1.90  tff(c_4686, plain, (![A_325, B_326]: (k4_xboole_0(k1_tarski(A_325), B_326)=k1_xboole_0 | ~r2_hidden(A_325, B_326))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4651])).
% 4.63/1.90  tff(c_2836, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_84])).
% 4.63/1.90  tff(c_82, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0 | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.90  tff(c_2886, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2836, c_82])).
% 4.63/1.90  tff(c_4719, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4686, c_2886])).
% 4.63/1.90  tff(c_4748, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2835, c_4719])).
% 4.63/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.90  
% 4.63/1.90  Inference rules
% 4.63/1.90  ----------------------
% 4.63/1.90  #Ref     : 0
% 4.63/1.90  #Sup     : 1105
% 4.63/1.90  #Fact    : 0
% 4.63/1.90  #Define  : 0
% 4.63/1.90  #Split   : 2
% 4.63/1.90  #Chain   : 0
% 4.63/1.90  #Close   : 0
% 4.63/1.90  
% 4.63/1.90  Ordering : KBO
% 4.63/1.90  
% 4.63/1.90  Simplification rules
% 4.63/1.90  ----------------------
% 4.63/1.90  #Subsume      : 95
% 4.63/1.90  #Demod        : 634
% 4.63/1.90  #Tautology    : 733
% 4.63/1.90  #SimpNegUnit  : 44
% 4.63/1.90  #BackRed      : 11
% 4.63/1.90  
% 4.63/1.90  #Partial instantiations: 0
% 4.63/1.90  #Strategies tried      : 1
% 4.63/1.90  
% 4.63/1.90  Timing (in seconds)
% 4.63/1.90  ----------------------
% 4.63/1.91  Preprocessing        : 0.36
% 4.63/1.91  Parsing              : 0.18
% 4.63/1.91  CNF conversion       : 0.03
% 4.63/1.91  Main loop            : 0.74
% 4.63/1.91  Inferencing          : 0.25
% 4.63/1.91  Reduction            : 0.29
% 4.63/1.91  Demodulation         : 0.23
% 4.63/1.91  BG Simplification    : 0.04
% 4.63/1.91  Subsumption          : 0.12
% 4.63/1.91  Abstraction          : 0.04
% 4.63/1.91  MUC search           : 0.00
% 4.63/1.91  Cooper               : 0.00
% 4.63/1.91  Total                : 1.14
% 4.63/1.91  Index Insertion      : 0.00
% 4.63/1.91  Index Deletion       : 0.00
% 4.63/1.91  Index Matching       : 0.00
% 4.63/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
