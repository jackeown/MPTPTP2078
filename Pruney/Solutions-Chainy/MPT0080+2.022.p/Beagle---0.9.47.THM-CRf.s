%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:52 EST 2020

% Result     : Theorem 27.17s
% Output     : CNFRefutation 27.17s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 240 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   15
%              Number of atoms          :  153 ( 497 expanded)
%              Number of equality atoms :   45 ( 133 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_40,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1607,plain,(
    ! [A_106,B_107,C_108] :
      ( r2_hidden('#skF_2'(A_106,B_107,C_108),A_106)
      | r2_hidden('#skF_3'(A_106,B_107,C_108),C_108)
      | k4_xboole_0(A_106,B_107) = C_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1659,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_3'(A_106,B_107,A_106),A_106)
      | k4_xboole_0(A_106,B_107) = A_106 ) ),
    inference(resolution,[status(thm)],[c_1607,c_22])).

tff(c_2261,plain,(
    ! [A_134,B_135,C_136] :
      ( r2_hidden('#skF_2'(A_134,B_135,C_136),A_134)
      | r2_hidden('#skF_3'(A_134,B_135,C_136),B_135)
      | ~ r2_hidden('#skF_3'(A_134,B_135,C_136),A_134)
      | k4_xboole_0(A_134,B_135) = C_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k4_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13796,plain,(
    ! [A_326,B_327] :
      ( r2_hidden('#skF_3'(A_326,B_327,A_326),B_327)
      | ~ r2_hidden('#skF_3'(A_326,B_327,A_326),A_326)
      | k4_xboole_0(A_326,B_327) = A_326 ) ),
    inference(resolution,[status(thm)],[c_2261,c_16])).

tff(c_14182,plain,(
    ! [A_335,B_336] :
      ( r2_hidden('#skF_3'(A_335,B_336,A_335),B_336)
      | k4_xboole_0(A_335,B_336) = A_335 ) ),
    inference(resolution,[status(thm)],[c_1659,c_13796])).

tff(c_2704,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_3'(A_152,B_153,A_152),A_152)
      | k4_xboole_0(A_152,B_153) = A_152 ) ),
    inference(resolution,[status(thm)],[c_1607,c_22])).

tff(c_112,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_1'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_118,plain,(
    ! [A_37] : r1_tarski(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_8,c_112])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_118,c_34])).

tff(c_130,plain,(
    ! [D_39,B_40,A_41] :
      ( ~ r2_hidden(D_39,B_40)
      | ~ r2_hidden(D_39,k4_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_133,plain,(
    ! [D_39,A_37] :
      ( ~ r2_hidden(D_39,A_37)
      | ~ r2_hidden(D_39,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_130])).

tff(c_2750,plain,(
    ! [A_152,B_153] :
      ( ~ r2_hidden('#skF_3'(A_152,B_153,A_152),k1_xboole_0)
      | k4_xboole_0(A_152,B_153) = A_152 ) ),
    inference(resolution,[status(thm)],[c_2704,c_133])).

tff(c_14260,plain,(
    ! [A_335] : k4_xboole_0(A_335,k1_xboole_0) = A_335 ),
    inference(resolution,[status(thm)],[c_14182,c_2750])).

tff(c_146,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_164,plain,(
    ! [A_37] : k4_xboole_0(A_37,k1_xboole_0) = k3_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_146])).

tff(c_14290,plain,(
    ! [A_37] : k3_xboole_0(A_37,A_37) = A_37 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14260,c_164])).

tff(c_339,plain,(
    ! [A_63,B_64,C_65] : k4_xboole_0(k4_xboole_0(A_63,B_64),C_65) = k4_xboole_0(A_63,k2_xboole_0(B_64,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_385,plain,(
    ! [A_37,C_65] : k4_xboole_0(k3_xboole_0(A_37,A_37),C_65) = k4_xboole_0(A_37,k2_xboole_0(k1_xboole_0,C_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_339])).

tff(c_16924,plain,(
    ! [A_365,C_366] : k4_xboole_0(A_365,k2_xboole_0(k1_xboole_0,C_366)) = k4_xboole_0(A_365,C_366) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14290,c_385])).

tff(c_42,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_518,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k2_xboole_0(B_70,k4_xboole_0(A_69,B_70))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_122])).

tff(c_578,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k2_xboole_0(k4_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_518])).

tff(c_3713,plain,(
    ! [A_178,B_179] : k4_xboole_0(A_178,k2_xboole_0(k3_xboole_0(A_178,B_179),k4_xboole_0(A_178,B_179))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_578])).

tff(c_3862,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_4','#skF_6'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_3713])).

tff(c_17069,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16924,c_3862])).

tff(c_10,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k4_xboole_0(A_8,B_9))
      | r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_55059,plain,(
    ! [D_662] :
      ( r2_hidden(D_662,k1_xboole_0)
      | r2_hidden(D_662,k4_xboole_0('#skF_4','#skF_6'))
      | ~ r2_hidden(D_662,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17069,c_10])).

tff(c_44,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_45,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_84,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    k4_xboole_0('#skF_4',k2_xboole_0('#skF_6','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_84])).

tff(c_36,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_709,plain,(
    ! [D_73,A_74,B_75] :
      ( r2_hidden(D_73,k4_xboole_0(A_74,B_75))
      | r2_hidden(D_73,B_75)
      | ~ r2_hidden(D_73,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12997,plain,(
    ! [D_313,A_314,B_315,C_316] :
      ( r2_hidden(D_313,k4_xboole_0(A_314,k2_xboole_0(B_315,C_316)))
      | r2_hidden(D_313,C_316)
      | ~ r2_hidden(D_313,k4_xboole_0(A_314,B_315)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_709])).

tff(c_13164,plain,(
    ! [D_313] :
      ( r2_hidden(D_313,k1_xboole_0)
      | r2_hidden(D_313,'#skF_5')
      | ~ r2_hidden(D_313,k4_xboole_0('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_12997])).

tff(c_55152,plain,(
    ! [D_662] :
      ( r2_hidden(D_662,'#skF_5')
      | r2_hidden(D_662,k1_xboole_0)
      | ~ r2_hidden(D_662,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_55059,c_13164])).

tff(c_211,plain,(
    ! [D_47,A_48,B_49] :
      ( r2_hidden(D_47,A_48)
      | ~ r2_hidden(D_47,k4_xboole_0(A_48,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_229,plain,(
    ! [D_50] :
      ( r2_hidden(D_50,'#skF_4')
      | ~ r2_hidden(D_50,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_211])).

tff(c_262,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_59),'#skF_4')
      | r1_tarski(k1_xboole_0,B_59) ) ),
    inference(resolution,[status(thm)],[c_8,c_229])).

tff(c_325,plain,(
    ! [B_61] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_61),k1_xboole_0)
      | r1_tarski(k1_xboole_0,B_61) ) ),
    inference(resolution,[status(thm)],[c_262,c_133])).

tff(c_330,plain,(
    ! [B_4] : r1_tarski(k1_xboole_0,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_325])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9974,plain,(
    ! [D_269,B_270,A_271,B_272] :
      ( r2_hidden(D_269,B_270)
      | ~ r1_tarski(k4_xboole_0(A_271,B_272),B_270)
      | r2_hidden(D_269,B_272)
      | ~ r2_hidden(D_269,A_271) ) ),
    inference(resolution,[status(thm)],[c_709,c_4])).

tff(c_10065,plain,(
    ! [D_269,B_270] :
      ( r2_hidden(D_269,B_270)
      | ~ r1_tarski(k1_xboole_0,B_270)
      | r2_hidden(D_269,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(D_269,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_9974])).

tff(c_10124,plain,(
    ! [D_269,B_270] :
      ( r2_hidden(D_269,B_270)
      | r2_hidden(D_269,k2_xboole_0('#skF_6','#skF_5'))
      | ~ r2_hidden(D_269,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_10065])).

tff(c_33643,plain,(
    ! [D_269] :
      ( ~ r2_hidden(D_269,'#skF_4')
      | r2_hidden(D_269,k2_xboole_0('#skF_6','#skF_5')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10124])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58591,plain,(
    ! [A_691,B_692,B_693] :
      ( r2_hidden('#skF_3'(A_691,B_692,A_691),B_693)
      | ~ r1_tarski(A_691,B_693)
      | k4_xboole_0(A_691,B_692) = A_691 ) ),
    inference(resolution,[status(thm)],[c_2704,c_4])).

tff(c_58769,plain,(
    ! [A_694,B_695] :
      ( ~ r1_tarski(A_694,k1_xboole_0)
      | k4_xboole_0(A_694,B_695) = A_694 ) ),
    inference(resolution,[status(thm)],[c_58591,c_2750])).

tff(c_58829,plain,(
    ! [A_16,B_695] :
      ( k4_xboole_0(A_16,B_695) = A_16
      | k4_xboole_0(A_16,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_58769])).

tff(c_58864,plain,(
    ! [A_696,B_697] :
      ( k4_xboole_0(A_696,B_697) = A_696
      | k1_xboole_0 != A_696 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14260,c_58829])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2856,plain,(
    ! [D_157,C_158,A_159,B_160] :
      ( ~ r2_hidden(D_157,C_158)
      | ~ r2_hidden(D_157,k4_xboole_0(A_159,k2_xboole_0(B_160,C_158))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_12])).

tff(c_2941,plain,(
    ! [D_157,A_1,A_159,B_2] :
      ( ~ r2_hidden(D_157,A_1)
      | ~ r2_hidden(D_157,k4_xboole_0(A_159,k2_xboole_0(A_1,B_2))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2856])).

tff(c_67930,plain,(
    ! [D_758,A_759,A_760] :
      ( ~ r2_hidden(D_758,A_759)
      | ~ r2_hidden(D_758,A_760)
      | k1_xboole_0 != A_760 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58864,c_2941])).

tff(c_77912,plain,(
    ! [D_812,A_813] :
      ( ~ r2_hidden(D_812,A_813)
      | k1_xboole_0 != A_813
      | ~ r2_hidden(D_812,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_33643,c_67930])).

tff(c_78054,plain,(
    ! [D_814] :
      ( r2_hidden(D_814,'#skF_5')
      | ~ r2_hidden(D_814,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_55152,c_77912])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87721,plain,(
    ! [A_920] :
      ( r1_tarski(A_920,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_920,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78054,c_6])).

tff(c_87741,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_87721])).

tff(c_87749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_87741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.17/16.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.17/16.70  
% 27.17/16.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.17/16.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 27.17/16.70  
% 27.17/16.70  %Foreground sorts:
% 27.17/16.70  
% 27.17/16.70  
% 27.17/16.70  %Background operators:
% 27.17/16.70  
% 27.17/16.70  
% 27.17/16.70  %Foreground operators:
% 27.17/16.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.17/16.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.17/16.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 27.17/16.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.17/16.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.17/16.70  tff('#skF_5', type, '#skF_5': $i).
% 27.17/16.70  tff('#skF_6', type, '#skF_6': $i).
% 27.17/16.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 27.17/16.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 27.17/16.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.17/16.70  tff('#skF_4', type, '#skF_4': $i).
% 27.17/16.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 27.17/16.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.17/16.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.17/16.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.17/16.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 27.17/16.70  
% 27.17/16.72  tff(f_63, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 27.17/16.72  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 27.17/16.72  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 27.17/16.72  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 27.17/16.72  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 27.17/16.72  tff(f_54, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 27.17/16.72  tff(f_48, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 27.17/16.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 27.17/16.72  tff(c_40, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 27.17/16.72  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.17/16.72  tff(c_1607, plain, (![A_106, B_107, C_108]: (r2_hidden('#skF_2'(A_106, B_107, C_108), A_106) | r2_hidden('#skF_3'(A_106, B_107, C_108), C_108) | k4_xboole_0(A_106, B_107)=C_108)), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_22, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_1659, plain, (![A_106, B_107]: (r2_hidden('#skF_3'(A_106, B_107, A_106), A_106) | k4_xboole_0(A_106, B_107)=A_106)), inference(resolution, [status(thm)], [c_1607, c_22])).
% 27.17/16.72  tff(c_2261, plain, (![A_134, B_135, C_136]: (r2_hidden('#skF_2'(A_134, B_135, C_136), A_134) | r2_hidden('#skF_3'(A_134, B_135, C_136), B_135) | ~r2_hidden('#skF_3'(A_134, B_135, C_136), A_134) | k4_xboole_0(A_134, B_135)=C_136)), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_16, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), B_9) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k4_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_13796, plain, (![A_326, B_327]: (r2_hidden('#skF_3'(A_326, B_327, A_326), B_327) | ~r2_hidden('#skF_3'(A_326, B_327, A_326), A_326) | k4_xboole_0(A_326, B_327)=A_326)), inference(resolution, [status(thm)], [c_2261, c_16])).
% 27.17/16.72  tff(c_14182, plain, (![A_335, B_336]: (r2_hidden('#skF_3'(A_335, B_336, A_335), B_336) | k4_xboole_0(A_335, B_336)=A_335)), inference(resolution, [status(thm)], [c_1659, c_13796])).
% 27.17/16.72  tff(c_2704, plain, (![A_152, B_153]: (r2_hidden('#skF_3'(A_152, B_153, A_152), A_152) | k4_xboole_0(A_152, B_153)=A_152)), inference(resolution, [status(thm)], [c_1607, c_22])).
% 27.17/16.72  tff(c_112, plain, (![A_35, B_36]: (~r2_hidden('#skF_1'(A_35, B_36), B_36) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.17/16.72  tff(c_118, plain, (![A_37]: (r1_tarski(A_37, A_37))), inference(resolution, [status(thm)], [c_8, c_112])).
% 27.17/16.72  tff(c_34, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.17/16.72  tff(c_122, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_118, c_34])).
% 27.17/16.72  tff(c_130, plain, (![D_39, B_40, A_41]: (~r2_hidden(D_39, B_40) | ~r2_hidden(D_39, k4_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_133, plain, (![D_39, A_37]: (~r2_hidden(D_39, A_37) | ~r2_hidden(D_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_122, c_130])).
% 27.17/16.72  tff(c_2750, plain, (![A_152, B_153]: (~r2_hidden('#skF_3'(A_152, B_153, A_152), k1_xboole_0) | k4_xboole_0(A_152, B_153)=A_152)), inference(resolution, [status(thm)], [c_2704, c_133])).
% 27.17/16.72  tff(c_14260, plain, (![A_335]: (k4_xboole_0(A_335, k1_xboole_0)=A_335)), inference(resolution, [status(thm)], [c_14182, c_2750])).
% 27.17/16.72  tff(c_146, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.17/16.72  tff(c_164, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=k3_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_122, c_146])).
% 27.17/16.72  tff(c_14290, plain, (![A_37]: (k3_xboole_0(A_37, A_37)=A_37)), inference(demodulation, [status(thm), theory('equality')], [c_14260, c_164])).
% 27.17/16.72  tff(c_339, plain, (![A_63, B_64, C_65]: (k4_xboole_0(k4_xboole_0(A_63, B_64), C_65)=k4_xboole_0(A_63, k2_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.17/16.72  tff(c_385, plain, (![A_37, C_65]: (k4_xboole_0(k3_xboole_0(A_37, A_37), C_65)=k4_xboole_0(A_37, k2_xboole_0(k1_xboole_0, C_65)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_339])).
% 27.17/16.72  tff(c_16924, plain, (![A_365, C_366]: (k4_xboole_0(A_365, k2_xboole_0(k1_xboole_0, C_366))=k4_xboole_0(A_365, C_366))), inference(demodulation, [status(thm), theory('equality')], [c_14290, c_385])).
% 27.17/16.72  tff(c_42, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 27.17/16.72  tff(c_79, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 27.17/16.72  tff(c_83, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_79])).
% 27.17/16.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 27.17/16.72  tff(c_38, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.17/16.72  tff(c_518, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k2_xboole_0(B_70, k4_xboole_0(A_69, B_70)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_339, c_122])).
% 27.17/16.72  tff(c_578, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k2_xboole_0(k4_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_518])).
% 27.17/16.72  tff(c_3713, plain, (![A_178, B_179]: (k4_xboole_0(A_178, k2_xboole_0(k3_xboole_0(A_178, B_179), k4_xboole_0(A_178, B_179)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_578])).
% 27.17/16.72  tff(c_3862, plain, (k4_xboole_0('#skF_4', k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_4', '#skF_6')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_83, c_3713])).
% 27.17/16.72  tff(c_17069, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16924, c_3862])).
% 27.17/16.72  tff(c_10, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, k4_xboole_0(A_8, B_9)) | r2_hidden(D_13, B_9) | ~r2_hidden(D_13, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_55059, plain, (![D_662]: (r2_hidden(D_662, k1_xboole_0) | r2_hidden(D_662, k4_xboole_0('#skF_4', '#skF_6')) | ~r2_hidden(D_662, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17069, c_10])).
% 27.17/16.72  tff(c_44, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 27.17/16.72  tff(c_45, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 27.17/16.72  tff(c_84, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.17/16.72  tff(c_88, plain, (k4_xboole_0('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_45, c_84])).
% 27.17/16.72  tff(c_36, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 27.17/16.72  tff(c_709, plain, (![D_73, A_74, B_75]: (r2_hidden(D_73, k4_xboole_0(A_74, B_75)) | r2_hidden(D_73, B_75) | ~r2_hidden(D_73, A_74))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_12997, plain, (![D_313, A_314, B_315, C_316]: (r2_hidden(D_313, k4_xboole_0(A_314, k2_xboole_0(B_315, C_316))) | r2_hidden(D_313, C_316) | ~r2_hidden(D_313, k4_xboole_0(A_314, B_315)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_709])).
% 27.17/16.72  tff(c_13164, plain, (![D_313]: (r2_hidden(D_313, k1_xboole_0) | r2_hidden(D_313, '#skF_5') | ~r2_hidden(D_313, k4_xboole_0('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_12997])).
% 27.17/16.72  tff(c_55152, plain, (![D_662]: (r2_hidden(D_662, '#skF_5') | r2_hidden(D_662, k1_xboole_0) | ~r2_hidden(D_662, '#skF_4'))), inference(resolution, [status(thm)], [c_55059, c_13164])).
% 27.17/16.72  tff(c_211, plain, (![D_47, A_48, B_49]: (r2_hidden(D_47, A_48) | ~r2_hidden(D_47, k4_xboole_0(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_229, plain, (![D_50]: (r2_hidden(D_50, '#skF_4') | ~r2_hidden(D_50, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_88, c_211])).
% 27.17/16.72  tff(c_262, plain, (![B_59]: (r2_hidden('#skF_1'(k1_xboole_0, B_59), '#skF_4') | r1_tarski(k1_xboole_0, B_59))), inference(resolution, [status(thm)], [c_8, c_229])).
% 27.17/16.72  tff(c_325, plain, (![B_61]: (~r2_hidden('#skF_1'(k1_xboole_0, B_61), k1_xboole_0) | r1_tarski(k1_xboole_0, B_61))), inference(resolution, [status(thm)], [c_262, c_133])).
% 27.17/16.72  tff(c_330, plain, (![B_4]: (r1_tarski(k1_xboole_0, B_4))), inference(resolution, [status(thm)], [c_8, c_325])).
% 27.17/16.72  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.17/16.72  tff(c_9974, plain, (![D_269, B_270, A_271, B_272]: (r2_hidden(D_269, B_270) | ~r1_tarski(k4_xboole_0(A_271, B_272), B_270) | r2_hidden(D_269, B_272) | ~r2_hidden(D_269, A_271))), inference(resolution, [status(thm)], [c_709, c_4])).
% 27.17/16.72  tff(c_10065, plain, (![D_269, B_270]: (r2_hidden(D_269, B_270) | ~r1_tarski(k1_xboole_0, B_270) | r2_hidden(D_269, k2_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(D_269, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_9974])).
% 27.17/16.72  tff(c_10124, plain, (![D_269, B_270]: (r2_hidden(D_269, B_270) | r2_hidden(D_269, k2_xboole_0('#skF_6', '#skF_5')) | ~r2_hidden(D_269, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_10065])).
% 27.17/16.72  tff(c_33643, plain, (![D_269]: (~r2_hidden(D_269, '#skF_4') | r2_hidden(D_269, k2_xboole_0('#skF_6', '#skF_5')))), inference(factorization, [status(thm), theory('equality')], [c_10124])).
% 27.17/16.72  tff(c_32, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | k4_xboole_0(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.17/16.72  tff(c_58591, plain, (![A_691, B_692, B_693]: (r2_hidden('#skF_3'(A_691, B_692, A_691), B_693) | ~r1_tarski(A_691, B_693) | k4_xboole_0(A_691, B_692)=A_691)), inference(resolution, [status(thm)], [c_2704, c_4])).
% 27.17/16.72  tff(c_58769, plain, (![A_694, B_695]: (~r1_tarski(A_694, k1_xboole_0) | k4_xboole_0(A_694, B_695)=A_694)), inference(resolution, [status(thm)], [c_58591, c_2750])).
% 27.17/16.72  tff(c_58829, plain, (![A_16, B_695]: (k4_xboole_0(A_16, B_695)=A_16 | k4_xboole_0(A_16, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_58769])).
% 27.17/16.72  tff(c_58864, plain, (![A_696, B_697]: (k4_xboole_0(A_696, B_697)=A_696 | k1_xboole_0!=A_696)), inference(demodulation, [status(thm), theory('equality')], [c_14260, c_58829])).
% 27.17/16.72  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.17/16.72  tff(c_2856, plain, (![D_157, C_158, A_159, B_160]: (~r2_hidden(D_157, C_158) | ~r2_hidden(D_157, k4_xboole_0(A_159, k2_xboole_0(B_160, C_158))))), inference(superposition, [status(thm), theory('equality')], [c_339, c_12])).
% 27.17/16.72  tff(c_2941, plain, (![D_157, A_1, A_159, B_2]: (~r2_hidden(D_157, A_1) | ~r2_hidden(D_157, k4_xboole_0(A_159, k2_xboole_0(A_1, B_2))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2856])).
% 27.17/16.72  tff(c_67930, plain, (![D_758, A_759, A_760]: (~r2_hidden(D_758, A_759) | ~r2_hidden(D_758, A_760) | k1_xboole_0!=A_760)), inference(superposition, [status(thm), theory('equality')], [c_58864, c_2941])).
% 27.17/16.72  tff(c_77912, plain, (![D_812, A_813]: (~r2_hidden(D_812, A_813) | k1_xboole_0!=A_813 | ~r2_hidden(D_812, '#skF_4'))), inference(resolution, [status(thm)], [c_33643, c_67930])).
% 27.17/16.72  tff(c_78054, plain, (![D_814]: (r2_hidden(D_814, '#skF_5') | ~r2_hidden(D_814, '#skF_4'))), inference(resolution, [status(thm)], [c_55152, c_77912])).
% 27.17/16.72  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 27.17/16.72  tff(c_87721, plain, (![A_920]: (r1_tarski(A_920, '#skF_5') | ~r2_hidden('#skF_1'(A_920, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_78054, c_6])).
% 27.17/16.72  tff(c_87741, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_87721])).
% 27.17/16.72  tff(c_87749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_87741])).
% 27.17/16.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.17/16.72  
% 27.17/16.72  Inference rules
% 27.17/16.72  ----------------------
% 27.17/16.72  #Ref     : 0
% 27.17/16.72  #Sup     : 22295
% 27.17/16.72  #Fact    : 2
% 27.17/16.72  #Define  : 0
% 27.17/16.72  #Split   : 4
% 27.17/16.72  #Chain   : 0
% 27.17/16.72  #Close   : 0
% 27.17/16.72  
% 27.17/16.72  Ordering : KBO
% 27.17/16.72  
% 27.17/16.72  Simplification rules
% 27.17/16.72  ----------------------
% 27.17/16.72  #Subsume      : 4735
% 27.17/16.72  #Demod        : 27225
% 27.17/16.72  #Tautology    : 9062
% 27.17/16.72  #SimpNegUnit  : 155
% 27.17/16.72  #BackRed      : 37
% 27.17/16.72  
% 27.17/16.72  #Partial instantiations: 0
% 27.17/16.72  #Strategies tried      : 1
% 27.17/16.72  
% 27.17/16.72  Timing (in seconds)
% 27.17/16.72  ----------------------
% 27.17/16.72  Preprocessing        : 0.29
% 27.17/16.72  Parsing              : 0.15
% 27.17/16.72  CNF conversion       : 0.02
% 27.17/16.72  Main loop            : 15.67
% 27.17/16.72  Inferencing          : 1.80
% 27.17/16.72  Reduction            : 9.70
% 27.17/16.72  Demodulation         : 8.77
% 27.17/16.72  BG Simplification    : 0.23
% 27.17/16.72  Subsumption          : 3.27
% 27.17/16.72  Abstraction          : 0.37
% 27.17/16.72  MUC search           : 0.00
% 27.17/16.72  Cooper               : 0.00
% 27.17/16.72  Total                : 16.00
% 27.17/16.72  Index Insertion      : 0.00
% 27.17/16.72  Index Deletion       : 0.00
% 27.17/16.72  Index Matching       : 0.00
% 27.17/16.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
