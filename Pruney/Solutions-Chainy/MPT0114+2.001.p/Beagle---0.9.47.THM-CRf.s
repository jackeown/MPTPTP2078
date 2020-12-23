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
% DateTime   : Thu Dec  3 09:45:24 EST 2020

% Result     : Theorem 30.82s
% Output     : CNFRefutation 31.11s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 681 expanded)
%              Number of leaves         :   31 ( 240 expanded)
%              Depth                    :   14
%              Number of atoms          :  233 ( 865 expanded)
%              Number of equality atoms :  127 ( 490 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k5_xboole_0(B,C))
      <=> ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_135836,plain,(
    ! [A_1416,B_1417] :
      ( r1_tarski(A_1416,B_1417)
      | k4_xboole_0(A_1416,B_1417) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_53,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_40])).

tff(c_589,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_16,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_196,plain,(
    ! [A_14,B_15] : k2_xboole_0(k4_xboole_0(A_14,B_15),A_14) = A_14 ),
    inference(resolution,[status(thm)],[c_20,c_180])).

tff(c_1227,plain,(
    ! [A_102,B_103,C_104] : k2_xboole_0(k4_xboole_0(A_102,B_103),k3_xboole_0(A_102,C_104)) = k4_xboole_0(A_102,k4_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1293,plain,(
    ! [A_11,B_103,B_12] : k4_xboole_0(A_11,k4_xboole_0(B_103,k2_xboole_0(A_11,B_12))) = k2_xboole_0(k4_xboole_0(A_11,B_103),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1227])).

tff(c_1310,plain,(
    ! [A_11,B_103,B_12] : k4_xboole_0(A_11,k4_xboole_0(B_103,k2_xboole_0(A_11,B_12))) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_1293])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(k2_xboole_0(A_7,B_8),k3_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22919,plain,(
    ! [A_354,B_355,C_356] : k4_xboole_0(k2_xboole_0(A_354,B_355),k4_xboole_0(k3_xboole_0(A_354,B_355),C_356)) = k2_xboole_0(k5_xboole_0(A_354,B_355),k3_xboole_0(k2_xboole_0(A_354,B_355),C_356)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1227])).

tff(c_23273,plain,(
    ! [A_354,B_355,B_12] : k2_xboole_0(k5_xboole_0(A_354,B_355),k3_xboole_0(k2_xboole_0(A_354,B_355),k2_xboole_0(k2_xboole_0(A_354,B_355),B_12))) = k2_xboole_0(A_354,B_355) ),
    inference(superposition,[status(thm),theory(equality)],[c_1310,c_22919])).

tff(c_26959,plain,(
    ! [A_401,B_402] : k2_xboole_0(k5_xboole_0(A_401,B_402),k2_xboole_0(A_401,B_402)) = k2_xboole_0(A_401,B_402) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_23273])).

tff(c_48,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_165,plain,(
    r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_195,plain,(
    k2_xboole_0('#skF_4',k5_xboole_0('#skF_5','#skF_6')) = k5_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_165,c_180])).

tff(c_26,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_336,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_377,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_336])).

tff(c_383,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_377])).

tff(c_167,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k2_xboole_0(A_44,B_45)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_172,plain,(
    ! [A_44] : r1_tarski(k1_xboole_0,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_20])).

tff(c_194,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(resolution,[status(thm)],[c_172,c_180])).

tff(c_72,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [A_40] : k3_xboole_0(k1_xboole_0,A_40) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_18])).

tff(c_649,plain,(
    ! [A_79,B_80] : k4_xboole_0(k2_xboole_0(A_79,B_80),k3_xboole_0(A_79,B_80)) = k5_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_685,plain,(
    ! [A_40] : k4_xboole_0(k2_xboole_0(k1_xboole_0,A_40),k1_xboole_0) = k5_xboole_0(k1_xboole_0,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_649])).

tff(c_704,plain,(
    ! [A_40] : k5_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_194,c_685])).

tff(c_558,plain,(
    ! [A_73,B_74] : r1_tarski(k3_xboole_0(A_73,B_74),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_20])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_583,plain,(
    ! [A_73,B_74] : k4_xboole_0(k3_xboole_0(A_73,B_74),A_73) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_558,c_24])).

tff(c_233,plain,(
    ! [A_55,B_56] : k2_xboole_0(k4_xboole_0(A_55,B_56),A_55) = A_55 ),
    inference(resolution,[status(thm)],[c_20,c_180])).

tff(c_239,plain,(
    ! [A_55,B_56] : k4_xboole_0(k4_xboole_0(A_55,B_56),A_55) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_26])).

tff(c_28,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_25,B_26] : k4_xboole_0(k2_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(k4_xboole_0(A_25,B_26),k4_xboole_0(B_26,A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_810,plain,(
    ! [A_88,B_89] : k2_xboole_0(k4_xboole_0(A_88,B_89),k4_xboole_0(B_89,A_88)) = k5_xboole_0(A_88,B_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_860,plain,(
    ! [A_20,B_21] : k2_xboole_0(k4_xboole_0(k4_xboole_0(A_20,B_21),A_20),k3_xboole_0(A_20,B_21)) = k5_xboole_0(k4_xboole_0(A_20,B_21),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_810])).

tff(c_3479,plain,(
    ! [A_159,B_160] : k5_xboole_0(k4_xboole_0(A_159,B_160),A_159) = k3_xboole_0(A_159,B_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_239,c_860])).

tff(c_3520,plain,(
    ! [A_73,B_74] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_73,B_74)) = k3_xboole_0(k3_xboole_0(A_73,B_74),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_3479])).

tff(c_3959,plain,(
    ! [A_167,B_168] : k3_xboole_0(k3_xboole_0(A_167,B_168),A_167) = k3_xboole_0(A_167,B_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_3520])).

tff(c_8166,plain,(
    ! [A_215,B_216] : k3_xboole_0(k3_xboole_0(A_215,B_216),B_216) = k3_xboole_0(B_216,A_215) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3959])).

tff(c_8356,plain,(
    ! [A_11,B_12] : k3_xboole_0(k2_xboole_0(A_11,B_12),A_11) = k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8166])).

tff(c_8421,plain,(
    ! [A_217,B_218] : k3_xboole_0(k2_xboole_0(A_217,B_218),A_217) = A_217 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8356])).

tff(c_8548,plain,(
    k3_xboole_0(k5_xboole_0('#skF_5','#skF_6'),'#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_8421])).

tff(c_8418,plain,(
    ! [A_11,B_12] : k3_xboole_0(k2_xboole_0(A_11,B_12),A_11) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8356])).

tff(c_11827,plain,(
    ! [A_251,B_252,C_253] : k3_xboole_0(k4_xboole_0(A_251,B_252),k4_xboole_0(A_251,k4_xboole_0(B_252,C_253))) = k4_xboole_0(A_251,B_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_1227,c_16])).

tff(c_12105,plain,(
    ! [B_252,C_253,B_56] : k3_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(B_252,C_253),B_56),B_252),k1_xboole_0) = k4_xboole_0(k4_xboole_0(k4_xboole_0(B_252,C_253),B_56),B_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_11827])).

tff(c_12589,plain,(
    ! [B_257,C_258,B_259] : k4_xboole_0(k4_xboole_0(k4_xboole_0(B_257,C_258),B_259),B_257) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12105])).

tff(c_193,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_180])).

tff(c_14192,plain,(
    ! [B_269,C_270,B_271] : k2_xboole_0(k4_xboole_0(k4_xboole_0(B_269,C_270),B_271),B_269) = B_269 ),
    inference(superposition,[status(thm),theory(equality)],[c_12589,c_193])).

tff(c_594,plain,(
    ! [B_75,A_76] : r1_tarski(k3_xboole_0(B_75,A_76),A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_558])).

tff(c_615,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_594])).

tff(c_14424,plain,(
    ! [B_272,C_273,B_274] : r1_tarski(k4_xboole_0(k4_xboole_0(B_272,C_273),B_274),B_272) ),
    inference(superposition,[status(thm),theory(equality)],[c_14192,c_615])).

tff(c_14606,plain,(
    ! [A_275,B_276,B_277] : r1_tarski(k4_xboole_0(k3_xboole_0(A_275,B_276),B_277),A_275) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_14424])).

tff(c_24838,plain,(
    ! [A_369,B_370,B_371] : r1_tarski(k4_xboole_0(A_369,B_370),k2_xboole_0(A_369,B_371)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8418,c_14606])).

tff(c_25290,plain,(
    ! [A_375,B_376,B_377] : r1_tarski(k3_xboole_0(A_375,B_376),k2_xboole_0(A_375,B_377)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_24838])).

tff(c_25355,plain,(
    ! [B_377] : r1_tarski('#skF_4',k2_xboole_0(k5_xboole_0('#skF_5','#skF_6'),B_377)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8548,c_25290])).

tff(c_26969,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26959,c_25355])).

tff(c_27164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_589,c_26969])).

tff(c_27166,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_38])).

tff(c_27209,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27166,c_50])).

tff(c_27210,plain,(
    ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_27209])).

tff(c_197,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(resolution,[status(thm)],[c_172,c_180])).

tff(c_203,plain,(
    ! [A_53] : k4_xboole_0(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_26])).

tff(c_27915,plain,(
    ! [A_430,B_431,C_432] : k2_xboole_0(k4_xboole_0(A_430,B_431),k3_xboole_0(A_430,C_432)) = k4_xboole_0(A_430,k4_xboole_0(B_431,C_432)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_27960,plain,(
    ! [A_18,C_432] : k4_xboole_0(A_18,k4_xboole_0(k1_xboole_0,C_432)) = k2_xboole_0(A_18,k3_xboole_0(A_18,C_432)) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_27915])).

tff(c_28008,plain,(
    ! [A_433,C_434] : k2_xboole_0(A_433,k3_xboole_0(A_433,C_434)) = A_433 ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_203,c_27960])).

tff(c_28058,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_28008])).

tff(c_27494,plain,(
    ! [A_417,B_418] : k4_xboole_0(k2_xboole_0(A_417,B_418),k3_xboole_0(A_417,B_418)) = k5_xboole_0(A_417,B_418) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27554,plain,(
    ! [A_13] : k4_xboole_0(k2_xboole_0(A_13,k1_xboole_0),k1_xboole_0) = k5_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_27494])).

tff(c_27563,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k2_xboole_0(A_13,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_27554])).

tff(c_28071,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28058,c_27563])).

tff(c_287,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_303,plain,(
    k4_xboole_0('#skF_4',k5_xboole_0('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_165,c_287])).

tff(c_27545,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),k3_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_27494])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_27174,plain,(
    k2_xboole_0('#skF_4',k2_xboole_0('#skF_5','#skF_6')) = k2_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_27166,c_14])).

tff(c_38305,plain,(
    ! [A_576,B_577,B_578] : k2_xboole_0(k4_xboole_0(A_576,B_577),k3_xboole_0(B_578,A_576)) = k4_xboole_0(A_576,k4_xboole_0(B_577,B_578)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_27915])).

tff(c_38507,plain,(
    ! [A_18,B_19,B_578] : k4_xboole_0(A_18,k4_xboole_0(k2_xboole_0(A_18,B_19),B_578)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_578,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_38305])).

tff(c_52985,plain,(
    ! [A_727,B_728,B_729] : k4_xboole_0(A_727,k4_xboole_0(k2_xboole_0(A_727,B_728),B_729)) = k3_xboole_0(B_729,A_727) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_38507])).

tff(c_53790,plain,(
    ! [B_732] : k4_xboole_0('#skF_4',k4_xboole_0(k2_xboole_0('#skF_5','#skF_6'),B_732)) = k3_xboole_0(B_732,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_27174,c_52985])).

tff(c_54064,plain,(
    k4_xboole_0('#skF_4',k5_xboole_0('#skF_5','#skF_6')) = k3_xboole_0(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_27545,c_53790])).

tff(c_54141,plain,(
    k3_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_303,c_54064])).

tff(c_30011,plain,(
    ! [A_482,B_483] : k3_xboole_0(k4_xboole_0(A_482,B_483),A_482) = k4_xboole_0(A_482,B_483) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_16])).

tff(c_30066,plain,(
    ! [A_482,B_483] : k3_xboole_0(A_482,k4_xboole_0(A_482,B_483)) = k4_xboole_0(A_482,B_483) ),
    inference(superposition,[status(thm),theory(equality)],[c_30011,c_4])).

tff(c_358,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,k4_xboole_0(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_336])).

tff(c_32683,plain,(
    ! [A_514,B_515] : k4_xboole_0(A_514,k3_xboole_0(A_514,B_515)) = k4_xboole_0(A_514,B_515) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30066,c_358])).

tff(c_49,plain,(
    ! [A_25,B_26] : k2_xboole_0(k4_xboole_0(A_25,B_26),k4_xboole_0(B_26,A_25)) = k5_xboole_0(A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_32749,plain,(
    ! [A_514,B_515] : k2_xboole_0(k4_xboole_0(A_514,B_515),k4_xboole_0(k3_xboole_0(A_514,B_515),A_514)) = k5_xboole_0(A_514,k3_xboole_0(A_514,B_515)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32683,c_49])).

tff(c_32850,plain,(
    ! [A_514,B_515] : k5_xboole_0(A_514,k3_xboole_0(A_514,B_515)) = k4_xboole_0(A_514,B_515) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28058,c_583,c_32749])).

tff(c_54259,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54141,c_32850])).

tff(c_54378,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28071,c_54259])).

tff(c_28000,plain,(
    ! [A_18,C_432] : k2_xboole_0(A_18,k3_xboole_0(A_18,C_432)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_203,c_27960])).

tff(c_384,plain,(
    ! [A_65] : k4_xboole_0(A_65,k1_xboole_0) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_377])).

tff(c_407,plain,(
    ! [A_65] : r1_tarski(A_65,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_20])).

tff(c_27987,plain,(
    ! [A_11,B_431,B_12] : k4_xboole_0(A_11,k4_xboole_0(B_431,k2_xboole_0(A_11,B_12))) = k2_xboole_0(k4_xboole_0(A_11,B_431),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_27915])).

tff(c_29258,plain,(
    ! [A_468,B_469,B_470] : k4_xboole_0(A_468,k4_xboole_0(B_469,k2_xboole_0(A_468,B_470))) = A_468 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_27987])).

tff(c_34,plain,(
    ! [A_27,C_29,B_28] :
      ( r1_xboole_0(A_27,k4_xboole_0(C_29,B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_77987,plain,(
    ! [A_867,A_868,B_869,B_870] :
      ( r1_xboole_0(A_867,A_868)
      | ~ r1_tarski(A_867,k4_xboole_0(B_869,k2_xboole_0(A_868,B_870))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29258,c_34])).

tff(c_78314,plain,(
    ! [B_873,A_874,B_875] : r1_xboole_0(k4_xboole_0(B_873,k2_xboole_0(A_874,B_875)),A_874) ),
    inference(resolution,[status(thm)],[c_407,c_77987])).

tff(c_78531,plain,(
    ! [B_876,A_877] : r1_xboole_0(k4_xboole_0(B_876,A_877),A_877) ),
    inference(superposition,[status(thm),theory(equality)],[c_28000,c_78314])).

tff(c_78623,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54378,c_78531])).

tff(c_78758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27210,c_78623])).

tff(c_78759,plain,(
    ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_27209])).

tff(c_78774,plain,(
    k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_78759])).

tff(c_42,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_51,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_78762,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27166,c_51])).

tff(c_78763,plain,(
    ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_78762])).

tff(c_78760,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_27209])).

tff(c_78768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78763,c_78760])).

tff(c_78770,plain,(
    r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_78762])).

tff(c_27165,plain,
    ( ~ r1_xboole_0('#skF_4',k3_xboole_0('#skF_6','#skF_5'))
    | r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_79081,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78770,c_27165])).

tff(c_79419,plain,(
    ! [A_898,B_899,C_900] :
      ( r1_tarski(A_898,k4_xboole_0(B_899,C_900))
      | ~ r1_xboole_0(A_898,C_900)
      | ~ r1_tarski(A_898,B_899) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_91904,plain,(
    ! [A_1058,B_1059,C_1060] :
      ( k4_xboole_0(A_1058,k4_xboole_0(B_1059,C_1060)) = k1_xboole_0
      | ~ r1_xboole_0(A_1058,C_1060)
      | ~ r1_tarski(A_1058,B_1059) ) ),
    inference(resolution,[status(thm)],[c_79419,c_24])).

tff(c_92094,plain,(
    ! [B_1059,C_1060] :
      ( k3_xboole_0(B_1059,C_1060) = k1_xboole_0
      | ~ r1_xboole_0(B_1059,C_1060)
      | ~ r1_tarski(B_1059,B_1059) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91904,c_28])).

tff(c_92379,plain,(
    ! [B_1061,C_1062] :
      ( k3_xboole_0(B_1061,C_1062) = k1_xboole_0
      | ~ r1_xboole_0(B_1061,C_1062) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_92094])).

tff(c_92405,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79081,c_92379])).

tff(c_79124,plain,(
    ! [A_890,B_891] : k4_xboole_0(k2_xboole_0(A_890,B_891),k3_xboole_0(A_890,B_891)) = k5_xboole_0(A_890,B_891) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79184,plain,(
    ! [B_4,A_3] : k4_xboole_0(k2_xboole_0(B_4,A_3),k3_xboole_0(A_3,B_4)) = k5_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_79124])).

tff(c_78769,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_78762])).

tff(c_78781,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78769,c_24])).

tff(c_79475,plain,(
    ! [A_901,B_902,C_903] : k2_xboole_0(k4_xboole_0(A_901,B_902),k3_xboole_0(A_901,C_903)) = k4_xboole_0(A_901,k4_xboole_0(B_902,C_903)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92970,plain,(
    ! [B_1063,B_1064,A_1065] : k2_xboole_0(k4_xboole_0(B_1063,B_1064),k3_xboole_0(A_1065,B_1063)) = k4_xboole_0(B_1063,k4_xboole_0(B_1064,A_1065)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_79475])).

tff(c_93184,plain,(
    ! [A_1065] : k4_xboole_0('#skF_1',k4_xboole_0(k2_xboole_0('#skF_2','#skF_3'),A_1065)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_1065,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78781,c_92970])).

tff(c_135362,plain,(
    ! [A_1410] : k4_xboole_0('#skF_1',k4_xboole_0(k2_xboole_0('#skF_2','#skF_3'),A_1410)) = k3_xboole_0(A_1410,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_93184])).

tff(c_135726,plain,(
    k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) = k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_79184,c_135362])).

tff(c_135817,plain,(
    k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92405,c_4,c_135726])).

tff(c_135819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78774,c_135817])).

tff(c_135821,plain,(
    ~ r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_135823,plain,(
    ~ r1_tarski('#skF_1',k5_xboole_0('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_135821,c_44])).

tff(c_135843,plain,(
    k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_135836,c_135823])).

tff(c_46,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,
    ( r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2'))
    | r1_tarski('#skF_4',k5_xboole_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_135908,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_135821,c_52])).

tff(c_136000,plain,(
    ! [A_1431,B_1432] : k4_xboole_0(A_1431,k4_xboole_0(A_1431,B_1432)) = k3_xboole_0(A_1431,B_1432) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_136044,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k4_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_136000])).

tff(c_136051,plain,(
    ! [A_1433] : k4_xboole_0(A_1433,k1_xboole_0) = A_1433 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_136044])).

tff(c_136077,plain,(
    ! [A_1433] : r1_tarski(A_1433,A_1433) ),
    inference(superposition,[status(thm),theory(equality)],[c_136051,c_20])).

tff(c_136683,plain,(
    ! [A_1462,B_1463,C_1464] :
      ( r1_tarski(A_1462,k4_xboole_0(B_1463,C_1464))
      | ~ r1_xboole_0(A_1462,C_1464)
      | ~ r1_tarski(A_1462,B_1463) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_149089,plain,(
    ! [A_1639,B_1640,C_1641] :
      ( k4_xboole_0(A_1639,k4_xboole_0(B_1640,C_1641)) = k1_xboole_0
      | ~ r1_xboole_0(A_1639,C_1641)
      | ~ r1_tarski(A_1639,B_1640) ) ),
    inference(resolution,[status(thm)],[c_136683,c_24])).

tff(c_149277,plain,(
    ! [B_1640,C_1641] :
      ( k3_xboole_0(B_1640,C_1641) = k1_xboole_0
      | ~ r1_xboole_0(B_1640,C_1641)
      | ~ r1_tarski(B_1640,B_1640) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149089,c_28])).

tff(c_149542,plain,(
    ! [B_1642,C_1643] :
      ( k3_xboole_0(B_1642,C_1643) = k1_xboole_0
      | ~ r1_xboole_0(B_1642,C_1643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136077,c_149277])).

tff(c_149567,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_135908,c_149542])).

tff(c_136559,plain,(
    ! [A_1459,B_1460] : k4_xboole_0(k2_xboole_0(A_1459,B_1460),k3_xboole_0(A_1459,B_1460)) = k5_xboole_0(A_1459,B_1460) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_136613,plain,(
    ! [B_4,A_3] : k4_xboole_0(k2_xboole_0(B_4,A_3),k3_xboole_0(A_3,B_4)) = k5_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_136559])).

tff(c_135820,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_135921,plain,(
    ! [A_1423,B_1424] :
      ( k2_xboole_0(A_1423,B_1424) = B_1424
      | ~ r1_tarski(A_1423,B_1424) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_135936,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_135820,c_135921])).

tff(c_135824,plain,(
    ! [A_1411,B_1412] : k4_xboole_0(A_1411,k2_xboole_0(A_1411,B_1412)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135829,plain,(
    ! [A_1411] : r1_tarski(k1_xboole_0,A_1411) ),
    inference(superposition,[status(thm),theory(equality)],[c_135824,c_20])).

tff(c_135935,plain,(
    ! [A_1411] : k2_xboole_0(k1_xboole_0,A_1411) = A_1411 ),
    inference(resolution,[status(thm)],[c_135829,c_135921])).

tff(c_136895,plain,(
    ! [A_1469,B_1470,C_1471] : k2_xboole_0(k4_xboole_0(A_1469,B_1470),k3_xboole_0(A_1469,C_1471)) = k4_xboole_0(A_1469,k4_xboole_0(B_1470,C_1471)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_146218,plain,(
    ! [A_1607,B_1608,B_1609] : k2_xboole_0(k4_xboole_0(A_1607,B_1608),k3_xboole_0(B_1609,A_1607)) = k4_xboole_0(A_1607,k4_xboole_0(B_1608,B_1609)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_136895])).

tff(c_146405,plain,(
    ! [A_18,B_19,B_1609] : k4_xboole_0(A_18,k4_xboole_0(k2_xboole_0(A_18,B_19),B_1609)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(B_1609,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_146218])).

tff(c_180781,plain,(
    ! [A_1897,B_1898,B_1899] : k4_xboole_0(A_1897,k4_xboole_0(k2_xboole_0(A_1897,B_1898),B_1899)) = k3_xboole_0(B_1899,A_1897) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135935,c_146405])).

tff(c_182088,plain,(
    ! [B_1902] : k4_xboole_0('#skF_1',k4_xboole_0(k2_xboole_0('#skF_2','#skF_3'),B_1902)) = k3_xboole_0(B_1902,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_135936,c_180781])).

tff(c_182391,plain,(
    k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) = k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_136613,c_182088])).

tff(c_182473,plain,(
    k4_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149567,c_4,c_182391])).

tff(c_182475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135843,c_182473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.82/21.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.94/21.18  
% 30.94/21.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.94/21.18  %$ r2_xboole_0 > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 30.94/21.18  
% 30.94/21.18  %Foreground sorts:
% 30.94/21.18  
% 30.94/21.18  
% 30.94/21.18  %Background operators:
% 30.94/21.18  
% 30.94/21.18  
% 30.94/21.18  %Foreground operators:
% 30.94/21.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.94/21.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 30.94/21.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.94/21.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 30.94/21.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.94/21.18  tff('#skF_5', type, '#skF_5': $i).
% 30.94/21.18  tff('#skF_6', type, '#skF_6': $i).
% 30.94/21.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 30.94/21.18  tff('#skF_2', type, '#skF_2': $i).
% 30.94/21.18  tff('#skF_3', type, '#skF_3': $i).
% 30.94/21.18  tff('#skF_1', type, '#skF_1': $i).
% 30.94/21.18  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 30.94/21.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.94/21.18  tff('#skF_4', type, '#skF_4': $i).
% 30.94/21.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.94/21.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 30.94/21.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.94/21.18  
% 31.11/21.21  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 31.11/21.21  tff(f_32, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 31.11/21.21  tff(f_80, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_xboole_1)).
% 31.11/21.21  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 31.11/21.21  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 31.11/21.21  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 31.11/21.21  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 31.11/21.21  tff(f_41, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 31.11/21.21  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 31.11/21.21  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 31.11/21.21  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 31.11/21.21  tff(f_63, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 31.11/21.21  tff(f_67, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 31.11/21.21  tff(f_73, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 31.11/21.21  tff(c_135836, plain, (![A_1416, B_1417]: (r1_tarski(A_1416, B_1417) | k4_xboole_0(A_1416, B_1417)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 31.11/21.21  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 31.11/21.21  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.11/21.21  tff(c_40, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 31.11/21.21  tff(c_53, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_40])).
% 31.11/21.21  tff(c_589, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_53])).
% 31.11/21.21  tff(c_16, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 31.11/21.21  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 31.11/21.21  tff(c_180, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 31.11/21.21  tff(c_196, plain, (![A_14, B_15]: (k2_xboole_0(k4_xboole_0(A_14, B_15), A_14)=A_14)), inference(resolution, [status(thm)], [c_20, c_180])).
% 31.11/21.21  tff(c_1227, plain, (![A_102, B_103, C_104]: (k2_xboole_0(k4_xboole_0(A_102, B_103), k3_xboole_0(A_102, C_104))=k4_xboole_0(A_102, k4_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.11/21.21  tff(c_1293, plain, (![A_11, B_103, B_12]: (k4_xboole_0(A_11, k4_xboole_0(B_103, k2_xboole_0(A_11, B_12)))=k2_xboole_0(k4_xboole_0(A_11, B_103), A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1227])).
% 31.11/21.21  tff(c_1310, plain, (![A_11, B_103, B_12]: (k4_xboole_0(A_11, k4_xboole_0(B_103, k2_xboole_0(A_11, B_12)))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_1293])).
% 31.11/21.21  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(k2_xboole_0(A_7, B_8), k3_xboole_0(A_7, B_8))=k5_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 31.11/21.21  tff(c_22919, plain, (![A_354, B_355, C_356]: (k4_xboole_0(k2_xboole_0(A_354, B_355), k4_xboole_0(k3_xboole_0(A_354, B_355), C_356))=k2_xboole_0(k5_xboole_0(A_354, B_355), k3_xboole_0(k2_xboole_0(A_354, B_355), C_356)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1227])).
% 31.11/21.21  tff(c_23273, plain, (![A_354, B_355, B_12]: (k2_xboole_0(k5_xboole_0(A_354, B_355), k3_xboole_0(k2_xboole_0(A_354, B_355), k2_xboole_0(k2_xboole_0(A_354, B_355), B_12)))=k2_xboole_0(A_354, B_355))), inference(superposition, [status(thm), theory('equality')], [c_1310, c_22919])).
% 31.11/21.21  tff(c_26959, plain, (![A_401, B_402]: (k2_xboole_0(k5_xboole_0(A_401, B_402), k2_xboole_0(A_401, B_402))=k2_xboole_0(A_401, B_402))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_23273])).
% 31.11/21.21  tff(c_48, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 31.11/21.21  tff(c_165, plain, (r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_48])).
% 31.11/21.21  tff(c_195, plain, (k2_xboole_0('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))=k5_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_165, c_180])).
% 31.11/21.21  tff(c_26, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.11/21.21  tff(c_336, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 31.11/21.21  tff(c_377, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k4_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_336])).
% 31.11/21.21  tff(c_383, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_377])).
% 31.11/21.21  tff(c_167, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k2_xboole_0(A_44, B_45))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.11/21.21  tff(c_172, plain, (![A_44]: (r1_tarski(k1_xboole_0, A_44))), inference(superposition, [status(thm), theory('equality')], [c_167, c_20])).
% 31.11/21.21  tff(c_194, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(resolution, [status(thm)], [c_172, c_180])).
% 31.11/21.21  tff(c_72, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)=k3_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.11/21.21  tff(c_18, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 31.11/21.21  tff(c_88, plain, (![A_40]: (k3_xboole_0(k1_xboole_0, A_40)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_72, c_18])).
% 31.11/21.21  tff(c_649, plain, (![A_79, B_80]: (k4_xboole_0(k2_xboole_0(A_79, B_80), k3_xboole_0(A_79, B_80))=k5_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_41])).
% 31.11/21.21  tff(c_685, plain, (![A_40]: (k4_xboole_0(k2_xboole_0(k1_xboole_0, A_40), k1_xboole_0)=k5_xboole_0(k1_xboole_0, A_40))), inference(superposition, [status(thm), theory('equality')], [c_88, c_649])).
% 31.11/21.21  tff(c_704, plain, (![A_40]: (k5_xboole_0(k1_xboole_0, A_40)=A_40)), inference(demodulation, [status(thm), theory('equality')], [c_383, c_194, c_685])).
% 31.11/21.21  tff(c_558, plain, (![A_73, B_74]: (r1_tarski(k3_xboole_0(A_73, B_74), A_73))), inference(superposition, [status(thm), theory('equality')], [c_336, c_20])).
% 31.11/21.21  tff(c_24, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 31.11/21.21  tff(c_583, plain, (![A_73, B_74]: (k4_xboole_0(k3_xboole_0(A_73, B_74), A_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_558, c_24])).
% 31.11/21.21  tff(c_233, plain, (![A_55, B_56]: (k2_xboole_0(k4_xboole_0(A_55, B_56), A_55)=A_55)), inference(resolution, [status(thm)], [c_20, c_180])).
% 31.11/21.21  tff(c_239, plain, (![A_55, B_56]: (k4_xboole_0(k4_xboole_0(A_55, B_56), A_55)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_233, c_26])).
% 31.11/21.21  tff(c_28, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 31.11/21.21  tff(c_32, plain, (![A_25, B_26]: (k4_xboole_0(k2_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(k4_xboole_0(A_25, B_26), k4_xboole_0(B_26, A_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 31.11/21.21  tff(c_810, plain, (![A_88, B_89]: (k2_xboole_0(k4_xboole_0(A_88, B_89), k4_xboole_0(B_89, A_88))=k5_xboole_0(A_88, B_89))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32])).
% 31.11/21.21  tff(c_860, plain, (![A_20, B_21]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(A_20, B_21), A_20), k3_xboole_0(A_20, B_21))=k5_xboole_0(k4_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_28, c_810])).
% 31.11/21.21  tff(c_3479, plain, (![A_159, B_160]: (k5_xboole_0(k4_xboole_0(A_159, B_160), A_159)=k3_xboole_0(A_159, B_160))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_239, c_860])).
% 31.11/21.21  tff(c_3520, plain, (![A_73, B_74]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_73, B_74))=k3_xboole_0(k3_xboole_0(A_73, B_74), A_73))), inference(superposition, [status(thm), theory('equality')], [c_583, c_3479])).
% 31.11/21.21  tff(c_3959, plain, (![A_167, B_168]: (k3_xboole_0(k3_xboole_0(A_167, B_168), A_167)=k3_xboole_0(A_167, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_3520])).
% 31.11/21.21  tff(c_8166, plain, (![A_215, B_216]: (k3_xboole_0(k3_xboole_0(A_215, B_216), B_216)=k3_xboole_0(B_216, A_215))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3959])).
% 31.11/21.21  tff(c_8356, plain, (![A_11, B_12]: (k3_xboole_0(k2_xboole_0(A_11, B_12), A_11)=k3_xboole_0(A_11, k2_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8166])).
% 31.11/21.21  tff(c_8421, plain, (![A_217, B_218]: (k3_xboole_0(k2_xboole_0(A_217, B_218), A_217)=A_217)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8356])).
% 31.11/21.21  tff(c_8548, plain, (k3_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_195, c_8421])).
% 31.11/21.21  tff(c_8418, plain, (![A_11, B_12]: (k3_xboole_0(k2_xboole_0(A_11, B_12), A_11)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8356])).
% 31.11/21.21  tff(c_11827, plain, (![A_251, B_252, C_253]: (k3_xboole_0(k4_xboole_0(A_251, B_252), k4_xboole_0(A_251, k4_xboole_0(B_252, C_253)))=k4_xboole_0(A_251, B_252))), inference(superposition, [status(thm), theory('equality')], [c_1227, c_16])).
% 31.11/21.21  tff(c_12105, plain, (![B_252, C_253, B_56]: (k3_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(B_252, C_253), B_56), B_252), k1_xboole_0)=k4_xboole_0(k4_xboole_0(k4_xboole_0(B_252, C_253), B_56), B_252))), inference(superposition, [status(thm), theory('equality')], [c_239, c_11827])).
% 31.11/21.21  tff(c_12589, plain, (![B_257, C_258, B_259]: (k4_xboole_0(k4_xboole_0(k4_xboole_0(B_257, C_258), B_259), B_257)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12105])).
% 31.11/21.21  tff(c_193, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_180])).
% 31.11/21.21  tff(c_14192, plain, (![B_269, C_270, B_271]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(B_269, C_270), B_271), B_269)=B_269)), inference(superposition, [status(thm), theory('equality')], [c_12589, c_193])).
% 31.11/21.21  tff(c_594, plain, (![B_75, A_76]: (r1_tarski(k3_xboole_0(B_75, A_76), A_76))), inference(superposition, [status(thm), theory('equality')], [c_4, c_558])).
% 31.11/21.21  tff(c_615, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_594])).
% 31.11/21.21  tff(c_14424, plain, (![B_272, C_273, B_274]: (r1_tarski(k4_xboole_0(k4_xboole_0(B_272, C_273), B_274), B_272))), inference(superposition, [status(thm), theory('equality')], [c_14192, c_615])).
% 31.11/21.21  tff(c_14606, plain, (![A_275, B_276, B_277]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_275, B_276), B_277), A_275))), inference(superposition, [status(thm), theory('equality')], [c_28, c_14424])).
% 31.11/21.21  tff(c_24838, plain, (![A_369, B_370, B_371]: (r1_tarski(k4_xboole_0(A_369, B_370), k2_xboole_0(A_369, B_371)))), inference(superposition, [status(thm), theory('equality')], [c_8418, c_14606])).
% 31.11/21.21  tff(c_25290, plain, (![A_375, B_376, B_377]: (r1_tarski(k3_xboole_0(A_375, B_376), k2_xboole_0(A_375, B_377)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_24838])).
% 31.11/21.21  tff(c_25355, plain, (![B_377]: (r1_tarski('#skF_4', k2_xboole_0(k5_xboole_0('#skF_5', '#skF_6'), B_377)))), inference(superposition, [status(thm), theory('equality')], [c_8548, c_25290])).
% 31.11/21.21  tff(c_26969, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_26959, c_25355])).
% 31.11/21.21  tff(c_27164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_589, c_26969])).
% 31.11/21.21  tff(c_27166, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_53])).
% 31.11/21.21  tff(c_38, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 31.11/21.21  tff(c_50, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_38])).
% 31.11/21.21  tff(c_27209, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27166, c_50])).
% 31.11/21.21  tff(c_27210, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_27209])).
% 31.11/21.21  tff(c_197, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(resolution, [status(thm)], [c_172, c_180])).
% 31.11/21.21  tff(c_203, plain, (![A_53]: (k4_xboole_0(k1_xboole_0, A_53)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_197, c_26])).
% 31.11/21.21  tff(c_27915, plain, (![A_430, B_431, C_432]: (k2_xboole_0(k4_xboole_0(A_430, B_431), k3_xboole_0(A_430, C_432))=k4_xboole_0(A_430, k4_xboole_0(B_431, C_432)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.11/21.21  tff(c_27960, plain, (![A_18, C_432]: (k4_xboole_0(A_18, k4_xboole_0(k1_xboole_0, C_432))=k2_xboole_0(A_18, k3_xboole_0(A_18, C_432)))), inference(superposition, [status(thm), theory('equality')], [c_383, c_27915])).
% 31.11/21.21  tff(c_28008, plain, (![A_433, C_434]: (k2_xboole_0(A_433, k3_xboole_0(A_433, C_434))=A_433)), inference(demodulation, [status(thm), theory('equality')], [c_383, c_203, c_27960])).
% 31.11/21.21  tff(c_28058, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(superposition, [status(thm), theory('equality')], [c_18, c_28008])).
% 31.11/21.21  tff(c_27494, plain, (![A_417, B_418]: (k4_xboole_0(k2_xboole_0(A_417, B_418), k3_xboole_0(A_417, B_418))=k5_xboole_0(A_417, B_418))), inference(cnfTransformation, [status(thm)], [f_41])).
% 31.11/21.21  tff(c_27554, plain, (![A_13]: (k4_xboole_0(k2_xboole_0(A_13, k1_xboole_0), k1_xboole_0)=k5_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_27494])).
% 31.11/21.21  tff(c_27563, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k2_xboole_0(A_13, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_27554])).
% 31.11/21.21  tff(c_28071, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_28058, c_27563])).
% 31.11/21.21  tff(c_287, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 31.11/21.21  tff(c_303, plain, (k4_xboole_0('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_165, c_287])).
% 31.11/21.21  tff(c_27545, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), k3_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_27494])).
% 31.11/21.21  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 31.11/21.21  tff(c_27174, plain, (k2_xboole_0('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))=k2_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_27166, c_14])).
% 31.11/21.21  tff(c_38305, plain, (![A_576, B_577, B_578]: (k2_xboole_0(k4_xboole_0(A_576, B_577), k3_xboole_0(B_578, A_576))=k4_xboole_0(A_576, k4_xboole_0(B_577, B_578)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_27915])).
% 31.11/21.21  tff(c_38507, plain, (![A_18, B_19, B_578]: (k4_xboole_0(A_18, k4_xboole_0(k2_xboole_0(A_18, B_19), B_578))=k2_xboole_0(k1_xboole_0, k3_xboole_0(B_578, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_38305])).
% 31.11/21.21  tff(c_52985, plain, (![A_727, B_728, B_729]: (k4_xboole_0(A_727, k4_xboole_0(k2_xboole_0(A_727, B_728), B_729))=k3_xboole_0(B_729, A_727))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_38507])).
% 31.11/21.21  tff(c_53790, plain, (![B_732]: (k4_xboole_0('#skF_4', k4_xboole_0(k2_xboole_0('#skF_5', '#skF_6'), B_732))=k3_xboole_0(B_732, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_27174, c_52985])).
% 31.11/21.21  tff(c_54064, plain, (k4_xboole_0('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))=k3_xboole_0(k3_xboole_0('#skF_6', '#skF_5'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_27545, c_53790])).
% 31.11/21.21  tff(c_54141, plain, (k3_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_303, c_54064])).
% 31.11/21.21  tff(c_30011, plain, (![A_482, B_483]: (k3_xboole_0(k4_xboole_0(A_482, B_483), A_482)=k4_xboole_0(A_482, B_483))), inference(superposition, [status(thm), theory('equality')], [c_233, c_16])).
% 31.11/21.21  tff(c_30066, plain, (![A_482, B_483]: (k3_xboole_0(A_482, k4_xboole_0(A_482, B_483))=k4_xboole_0(A_482, B_483))), inference(superposition, [status(thm), theory('equality')], [c_30011, c_4])).
% 31.11/21.21  tff(c_358, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k3_xboole_0(A_20, k4_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_336])).
% 31.11/21.21  tff(c_32683, plain, (![A_514, B_515]: (k4_xboole_0(A_514, k3_xboole_0(A_514, B_515))=k4_xboole_0(A_514, B_515))), inference(demodulation, [status(thm), theory('equality')], [c_30066, c_358])).
% 31.11/21.21  tff(c_49, plain, (![A_25, B_26]: (k2_xboole_0(k4_xboole_0(A_25, B_26), k4_xboole_0(B_26, A_25))=k5_xboole_0(A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_32])).
% 31.11/21.21  tff(c_32749, plain, (![A_514, B_515]: (k2_xboole_0(k4_xboole_0(A_514, B_515), k4_xboole_0(k3_xboole_0(A_514, B_515), A_514))=k5_xboole_0(A_514, k3_xboole_0(A_514, B_515)))), inference(superposition, [status(thm), theory('equality')], [c_32683, c_49])).
% 31.11/21.21  tff(c_32850, plain, (![A_514, B_515]: (k5_xboole_0(A_514, k3_xboole_0(A_514, B_515))=k4_xboole_0(A_514, B_515))), inference(demodulation, [status(thm), theory('equality')], [c_28058, c_583, c_32749])).
% 31.11/21.21  tff(c_54259, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54141, c_32850])).
% 31.11/21.21  tff(c_54378, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28071, c_54259])).
% 31.11/21.21  tff(c_28000, plain, (![A_18, C_432]: (k2_xboole_0(A_18, k3_xboole_0(A_18, C_432))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_383, c_203, c_27960])).
% 31.11/21.21  tff(c_384, plain, (![A_65]: (k4_xboole_0(A_65, k1_xboole_0)=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_377])).
% 31.11/21.21  tff(c_407, plain, (![A_65]: (r1_tarski(A_65, A_65))), inference(superposition, [status(thm), theory('equality')], [c_384, c_20])).
% 31.11/21.21  tff(c_27987, plain, (![A_11, B_431, B_12]: (k4_xboole_0(A_11, k4_xboole_0(B_431, k2_xboole_0(A_11, B_12)))=k2_xboole_0(k4_xboole_0(A_11, B_431), A_11))), inference(superposition, [status(thm), theory('equality')], [c_16, c_27915])).
% 31.11/21.21  tff(c_29258, plain, (![A_468, B_469, B_470]: (k4_xboole_0(A_468, k4_xboole_0(B_469, k2_xboole_0(A_468, B_470)))=A_468)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_27987])).
% 31.11/21.21  tff(c_34, plain, (![A_27, C_29, B_28]: (r1_xboole_0(A_27, k4_xboole_0(C_29, B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 31.11/21.21  tff(c_77987, plain, (![A_867, A_868, B_869, B_870]: (r1_xboole_0(A_867, A_868) | ~r1_tarski(A_867, k4_xboole_0(B_869, k2_xboole_0(A_868, B_870))))), inference(superposition, [status(thm), theory('equality')], [c_29258, c_34])).
% 31.11/21.21  tff(c_78314, plain, (![B_873, A_874, B_875]: (r1_xboole_0(k4_xboole_0(B_873, k2_xboole_0(A_874, B_875)), A_874))), inference(resolution, [status(thm)], [c_407, c_77987])).
% 31.11/21.21  tff(c_78531, plain, (![B_876, A_877]: (r1_xboole_0(k4_xboole_0(B_876, A_877), A_877))), inference(superposition, [status(thm), theory('equality')], [c_28000, c_78314])).
% 31.11/21.21  tff(c_78623, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_54378, c_78531])).
% 31.11/21.21  tff(c_78758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27210, c_78623])).
% 31.11/21.21  tff(c_78759, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_27209])).
% 31.11/21.21  tff(c_78774, plain, (k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_78759])).
% 31.11/21.21  tff(c_42, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 31.11/21.21  tff(c_51, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_42])).
% 31.11/21.21  tff(c_78762, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27166, c_51])).
% 31.11/21.21  tff(c_78763, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_78762])).
% 31.11/21.21  tff(c_78760, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_27209])).
% 31.11/21.21  tff(c_78768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78763, c_78760])).
% 31.11/21.21  tff(c_78770, plain, (r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_78762])).
% 31.11/21.21  tff(c_27165, plain, (~r1_xboole_0('#skF_4', k3_xboole_0('#skF_6', '#skF_5')) | r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_53])).
% 31.11/21.21  tff(c_79081, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78770, c_27165])).
% 31.11/21.21  tff(c_79419, plain, (![A_898, B_899, C_900]: (r1_tarski(A_898, k4_xboole_0(B_899, C_900)) | ~r1_xboole_0(A_898, C_900) | ~r1_tarski(A_898, B_899))), inference(cnfTransformation, [status(thm)], [f_73])).
% 31.11/21.21  tff(c_91904, plain, (![A_1058, B_1059, C_1060]: (k4_xboole_0(A_1058, k4_xboole_0(B_1059, C_1060))=k1_xboole_0 | ~r1_xboole_0(A_1058, C_1060) | ~r1_tarski(A_1058, B_1059))), inference(resolution, [status(thm)], [c_79419, c_24])).
% 31.11/21.21  tff(c_92094, plain, (![B_1059, C_1060]: (k3_xboole_0(B_1059, C_1060)=k1_xboole_0 | ~r1_xboole_0(B_1059, C_1060) | ~r1_tarski(B_1059, B_1059))), inference(superposition, [status(thm), theory('equality')], [c_91904, c_28])).
% 31.11/21.21  tff(c_92379, plain, (![B_1061, C_1062]: (k3_xboole_0(B_1061, C_1062)=k1_xboole_0 | ~r1_xboole_0(B_1061, C_1062))), inference(demodulation, [status(thm), theory('equality')], [c_407, c_92094])).
% 31.11/21.21  tff(c_92405, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_79081, c_92379])).
% 31.11/21.21  tff(c_79124, plain, (![A_890, B_891]: (k4_xboole_0(k2_xboole_0(A_890, B_891), k3_xboole_0(A_890, B_891))=k5_xboole_0(A_890, B_891))), inference(cnfTransformation, [status(thm)], [f_41])).
% 31.11/21.21  tff(c_79184, plain, (![B_4, A_3]: (k4_xboole_0(k2_xboole_0(B_4, A_3), k3_xboole_0(A_3, B_4))=k5_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_79124])).
% 31.11/21.21  tff(c_78769, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_78762])).
% 31.11/21.21  tff(c_78781, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_78769, c_24])).
% 31.11/21.21  tff(c_79475, plain, (![A_901, B_902, C_903]: (k2_xboole_0(k4_xboole_0(A_901, B_902), k3_xboole_0(A_901, C_903))=k4_xboole_0(A_901, k4_xboole_0(B_902, C_903)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.11/21.21  tff(c_92970, plain, (![B_1063, B_1064, A_1065]: (k2_xboole_0(k4_xboole_0(B_1063, B_1064), k3_xboole_0(A_1065, B_1063))=k4_xboole_0(B_1063, k4_xboole_0(B_1064, A_1065)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_79475])).
% 31.11/21.21  tff(c_93184, plain, (![A_1065]: (k4_xboole_0('#skF_1', k4_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), A_1065))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_1065, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_78781, c_92970])).
% 31.11/21.21  tff(c_135362, plain, (![A_1410]: (k4_xboole_0('#skF_1', k4_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), A_1410))=k3_xboole_0(A_1410, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_93184])).
% 31.11/21.21  tff(c_135726, plain, (k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_79184, c_135362])).
% 31.11/21.21  tff(c_135817, plain, (k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92405, c_4, c_135726])).
% 31.11/21.21  tff(c_135819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78774, c_135817])).
% 31.11/21.21  tff(c_135821, plain, (~r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_48])).
% 31.11/21.21  tff(c_44, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 31.11/21.21  tff(c_135823, plain, (~r1_tarski('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_135821, c_44])).
% 31.11/21.21  tff(c_135843, plain, (k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_135836, c_135823])).
% 31.11/21.21  tff(c_46, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 31.11/21.21  tff(c_52, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2')) | r1_tarski('#skF_4', k5_xboole_0('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_46])).
% 31.11/21.21  tff(c_135908, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_135821, c_52])).
% 31.11/21.21  tff(c_136000, plain, (![A_1431, B_1432]: (k4_xboole_0(A_1431, k4_xboole_0(A_1431, B_1432))=k3_xboole_0(A_1431, B_1432))), inference(cnfTransformation, [status(thm)], [f_59])).
% 31.11/21.21  tff(c_136044, plain, (![A_18, B_19]: (k3_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k4_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_136000])).
% 31.11/21.21  tff(c_136051, plain, (![A_1433]: (k4_xboole_0(A_1433, k1_xboole_0)=A_1433)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_136044])).
% 31.11/21.21  tff(c_136077, plain, (![A_1433]: (r1_tarski(A_1433, A_1433))), inference(superposition, [status(thm), theory('equality')], [c_136051, c_20])).
% 31.11/21.21  tff(c_136683, plain, (![A_1462, B_1463, C_1464]: (r1_tarski(A_1462, k4_xboole_0(B_1463, C_1464)) | ~r1_xboole_0(A_1462, C_1464) | ~r1_tarski(A_1462, B_1463))), inference(cnfTransformation, [status(thm)], [f_73])).
% 31.11/21.21  tff(c_149089, plain, (![A_1639, B_1640, C_1641]: (k4_xboole_0(A_1639, k4_xboole_0(B_1640, C_1641))=k1_xboole_0 | ~r1_xboole_0(A_1639, C_1641) | ~r1_tarski(A_1639, B_1640))), inference(resolution, [status(thm)], [c_136683, c_24])).
% 31.11/21.21  tff(c_149277, plain, (![B_1640, C_1641]: (k3_xboole_0(B_1640, C_1641)=k1_xboole_0 | ~r1_xboole_0(B_1640, C_1641) | ~r1_tarski(B_1640, B_1640))), inference(superposition, [status(thm), theory('equality')], [c_149089, c_28])).
% 31.11/21.21  tff(c_149542, plain, (![B_1642, C_1643]: (k3_xboole_0(B_1642, C_1643)=k1_xboole_0 | ~r1_xboole_0(B_1642, C_1643))), inference(demodulation, [status(thm), theory('equality')], [c_136077, c_149277])).
% 31.11/21.21  tff(c_149567, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_135908, c_149542])).
% 31.11/21.21  tff(c_136559, plain, (![A_1459, B_1460]: (k4_xboole_0(k2_xboole_0(A_1459, B_1460), k3_xboole_0(A_1459, B_1460))=k5_xboole_0(A_1459, B_1460))), inference(cnfTransformation, [status(thm)], [f_41])).
% 31.11/21.21  tff(c_136613, plain, (![B_4, A_3]: (k4_xboole_0(k2_xboole_0(B_4, A_3), k3_xboole_0(A_3, B_4))=k5_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_136559])).
% 31.11/21.21  tff(c_135820, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 31.11/21.21  tff(c_135921, plain, (![A_1423, B_1424]: (k2_xboole_0(A_1423, B_1424)=B_1424 | ~r1_tarski(A_1423, B_1424))), inference(cnfTransformation, [status(thm)], [f_45])).
% 31.11/21.21  tff(c_135936, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_135820, c_135921])).
% 31.11/21.21  tff(c_135824, plain, (![A_1411, B_1412]: (k4_xboole_0(A_1411, k2_xboole_0(A_1411, B_1412))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 31.11/21.21  tff(c_135829, plain, (![A_1411]: (r1_tarski(k1_xboole_0, A_1411))), inference(superposition, [status(thm), theory('equality')], [c_135824, c_20])).
% 31.11/21.21  tff(c_135935, plain, (![A_1411]: (k2_xboole_0(k1_xboole_0, A_1411)=A_1411)), inference(resolution, [status(thm)], [c_135829, c_135921])).
% 31.11/21.21  tff(c_136895, plain, (![A_1469, B_1470, C_1471]: (k2_xboole_0(k4_xboole_0(A_1469, B_1470), k3_xboole_0(A_1469, C_1471))=k4_xboole_0(A_1469, k4_xboole_0(B_1470, C_1471)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.11/21.21  tff(c_146218, plain, (![A_1607, B_1608, B_1609]: (k2_xboole_0(k4_xboole_0(A_1607, B_1608), k3_xboole_0(B_1609, A_1607))=k4_xboole_0(A_1607, k4_xboole_0(B_1608, B_1609)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_136895])).
% 31.11/21.21  tff(c_146405, plain, (![A_18, B_19, B_1609]: (k4_xboole_0(A_18, k4_xboole_0(k2_xboole_0(A_18, B_19), B_1609))=k2_xboole_0(k1_xboole_0, k3_xboole_0(B_1609, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_146218])).
% 31.11/21.21  tff(c_180781, plain, (![A_1897, B_1898, B_1899]: (k4_xboole_0(A_1897, k4_xboole_0(k2_xboole_0(A_1897, B_1898), B_1899))=k3_xboole_0(B_1899, A_1897))), inference(demodulation, [status(thm), theory('equality')], [c_135935, c_146405])).
% 31.11/21.21  tff(c_182088, plain, (![B_1902]: (k4_xboole_0('#skF_1', k4_xboole_0(k2_xboole_0('#skF_2', '#skF_3'), B_1902))=k3_xboole_0(B_1902, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_135936, c_180781])).
% 31.11/21.21  tff(c_182391, plain, (k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))=k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_136613, c_182088])).
% 31.11/21.21  tff(c_182473, plain, (k4_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_149567, c_4, c_182391])).
% 31.11/21.21  tff(c_182475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135843, c_182473])).
% 31.11/21.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.11/21.21  
% 31.11/21.21  Inference rules
% 31.11/21.21  ----------------------
% 31.11/21.21  #Ref     : 4
% 31.11/21.21  #Sup     : 46861
% 31.11/21.21  #Fact    : 0
% 31.11/21.21  #Define  : 0
% 31.11/21.21  #Split   : 39
% 31.11/21.21  #Chain   : 0
% 31.11/21.21  #Close   : 0
% 31.11/21.21  
% 31.11/21.21  Ordering : KBO
% 31.11/21.21  
% 31.11/21.21  Simplification rules
% 31.11/21.21  ----------------------
% 31.11/21.21  #Subsume      : 4257
% 31.11/21.21  #Demod        : 47976
% 31.11/21.21  #Tautology    : 28057
% 31.11/21.21  #SimpNegUnit  : 299
% 31.11/21.21  #BackRed      : 49
% 31.11/21.21  
% 31.11/21.21  #Partial instantiations: 0
% 31.11/21.21  #Strategies tried      : 1
% 31.11/21.21  
% 31.11/21.21  Timing (in seconds)
% 31.11/21.21  ----------------------
% 31.11/21.22  Preprocessing        : 0.31
% 31.11/21.22  Parsing              : 0.16
% 31.11/21.22  CNF conversion       : 0.02
% 31.11/21.22  Main loop            : 20.10
% 31.11/21.22  Inferencing          : 2.53
% 31.11/21.22  Reduction            : 12.84
% 31.11/21.22  Demodulation         : 11.43
% 31.11/21.22  BG Simplification    : 0.31
% 31.11/21.22  Subsumption          : 3.52
% 31.11/21.22  Abstraction          : 0.62
% 31.11/21.22  MUC search           : 0.00
% 31.11/21.22  Cooper               : 0.00
% 31.11/21.22  Total                : 20.48
% 31.11/21.22  Index Insertion      : 0.00
% 31.11/21.22  Index Deletion       : 0.00
% 31.11/21.22  Index Matching       : 0.00
% 31.11/21.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
