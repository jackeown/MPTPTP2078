%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:30 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 210 expanded)
%              Number of leaves         :   23 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          :  206 ( 561 expanded)
%              Number of equality atoms :    4 (  30 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_6 > #skF_2 > #skF_4 > #skF_7 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_68,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v8_relat_2(A)
      <=> ! [B,C,D] :
            ( ( r2_hidden(k4_tarski(B,C),A)
              & r2_hidden(k4_tarski(C,D),A) )
           => r2_hidden(k4_tarski(B,D),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] : v8_relat_2(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

tff(c_38,plain,(
    ! [A_27] : v1_relat_1(k1_wellord2(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden('#skF_1'(A_32,B_33),B_33)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_32,plain,(
    ! [A_19] :
      ( k3_relat_1(k1_wellord2(A_19)) = A_19
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,(
    ! [A_19] : k3_relat_1(k1_wellord2(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_70,plain,(
    ! [A_41] :
      ( r2_hidden(k4_tarski('#skF_3'(A_41),'#skF_4'(A_41)),A_41)
      | v8_relat_2(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_208,plain,(
    ! [A_72,B_73] :
      ( r2_hidden(k4_tarski('#skF_3'(A_72),'#skF_4'(A_72)),B_73)
      | ~ r1_tarski(A_72,B_73)
      | v8_relat_2(A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_8,plain,(
    ! [B_7,C_8,A_6] :
      ( r2_hidden(B_7,k3_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_250,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_4'(A_86),k3_relat_1(B_87))
      | ~ v1_relat_1(B_87)
      | ~ r1_tarski(A_86,B_87)
      | v8_relat_2(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_208,c_8])).

tff(c_255,plain,(
    ! [A_86,A_19] :
      ( r2_hidden('#skF_4'(A_86),A_19)
      | ~ v1_relat_1(k1_wellord2(A_19))
      | ~ r1_tarski(A_86,k1_wellord2(A_19))
      | v8_relat_2(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_250])).

tff(c_258,plain,(
    ! [A_86,A_19] :
      ( r2_hidden('#skF_4'(A_86),A_19)
      | ~ r1_tarski(A_86,k1_wellord2(A_19))
      | v8_relat_2(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_255])).

tff(c_78,plain,(
    ! [A_42] :
      ( r2_hidden(k4_tarski('#skF_2'(A_42),'#skF_3'(A_42)),A_42)
      | v8_relat_2(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_196,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(k4_tarski('#skF_2'(A_70),'#skF_3'(A_70)),B_71)
      | ~ r1_tarski(A_70,B_71)
      | v8_relat_2(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r2_hidden(A_6,k3_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_291,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_2'(A_93),k3_relat_1(B_94))
      | ~ v1_relat_1(B_94)
      | ~ r1_tarski(A_93,B_94)
      | v8_relat_2(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_196,c_10])).

tff(c_296,plain,(
    ! [A_93,A_19] :
      ( r2_hidden('#skF_2'(A_93),A_19)
      | ~ v1_relat_1(k1_wellord2(A_19))
      | ~ r1_tarski(A_93,k1_wellord2(A_19))
      | v8_relat_2(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_291])).

tff(c_299,plain,(
    ! [A_93,A_19] :
      ( r2_hidden('#skF_2'(A_93),A_19)
      | ~ r1_tarski(A_93,k1_wellord2(A_19))
      | v8_relat_2(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_296])).

tff(c_86,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_3'(A_43),k3_relat_1(A_43))
      | v8_relat_2(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_70,c_10])).

tff(c_91,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_19)),A_19)
      | v8_relat_2(k1_wellord2(A_19))
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_86])).

tff(c_94,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_3'(k1_wellord2(A_19)),A_19)
      | v8_relat_2(k1_wellord2(A_19)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_91])).

tff(c_77,plain,(
    ! [A_41,B_2] :
      ( r2_hidden(k4_tarski('#skF_3'(A_41),'#skF_4'(A_41)),B_2)
      | ~ r1_tarski(A_41,B_2)
      | v8_relat_2(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(resolution,[status(thm)],[c_70,c_2])).

tff(c_36,plain,(
    ! [C_25,D_26,A_19] :
      ( r1_tarski(C_25,D_26)
      | ~ r2_hidden(k4_tarski(C_25,D_26),k1_wellord2(A_19))
      | ~ r2_hidden(D_26,A_19)
      | ~ r2_hidden(C_25,A_19)
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_334,plain,(
    ! [C_107,D_108,A_109] :
      ( r1_tarski(C_107,D_108)
      | ~ r2_hidden(k4_tarski(C_107,D_108),k1_wellord2(A_109))
      | ~ r2_hidden(D_108,A_109)
      | ~ r2_hidden(C_107,A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_978,plain,(
    ! [A_210,A_211] :
      ( r1_tarski('#skF_3'(A_210),'#skF_4'(A_210))
      | ~ r2_hidden('#skF_4'(A_210),A_211)
      | ~ r2_hidden('#skF_3'(A_210),A_211)
      | ~ r1_tarski(A_210,k1_wellord2(A_211))
      | v8_relat_2(A_210)
      | ~ v1_relat_1(A_210) ) ),
    inference(resolution,[status(thm)],[c_77,c_334])).

tff(c_1061,plain,(
    ! [A_213,A_214] :
      ( r1_tarski('#skF_3'(A_213),'#skF_4'(A_213))
      | ~ r2_hidden('#skF_3'(A_213),A_214)
      | ~ r1_tarski(A_213,k1_wellord2(A_214))
      | v8_relat_2(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(resolution,[status(thm)],[c_258,c_978])).

tff(c_1077,plain,(
    ! [A_19] :
      ( r1_tarski('#skF_3'(k1_wellord2(A_19)),'#skF_4'(k1_wellord2(A_19)))
      | ~ r1_tarski(k1_wellord2(A_19),k1_wellord2(A_19))
      | ~ v1_relat_1(k1_wellord2(A_19))
      | v8_relat_2(k1_wellord2(A_19)) ) ),
    inference(resolution,[status(thm)],[c_94,c_1061])).

tff(c_1095,plain,(
    ! [A_215] :
      ( r1_tarski('#skF_3'(k1_wellord2(A_215)),'#skF_4'(k1_wellord2(A_215)))
      | v8_relat_2(k1_wellord2(A_215)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_1077])).

tff(c_85,plain,(
    ! [A_42,B_2] :
      ( r2_hidden(k4_tarski('#skF_2'(A_42),'#skF_3'(A_42)),B_2)
      | ~ r1_tarski(A_42,B_2)
      | v8_relat_2(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_576,plain,(
    ! [A_161,A_162] :
      ( r1_tarski('#skF_2'(A_161),'#skF_3'(A_161))
      | ~ r2_hidden('#skF_3'(A_161),A_162)
      | ~ r2_hidden('#skF_2'(A_161),A_162)
      | ~ r1_tarski(A_161,k1_wellord2(A_162))
      | v8_relat_2(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(resolution,[status(thm)],[c_85,c_334])).

tff(c_672,plain,(
    ! [A_168,A_169] :
      ( r1_tarski('#skF_2'(A_168),'#skF_3'(A_168))
      | ~ r2_hidden('#skF_3'(A_168),A_169)
      | ~ r1_tarski(A_168,k1_wellord2(A_169))
      | v8_relat_2(A_168)
      | ~ v1_relat_1(A_168) ) ),
    inference(resolution,[status(thm)],[c_299,c_576])).

tff(c_682,plain,(
    ! [A_19] :
      ( r1_tarski('#skF_2'(k1_wellord2(A_19)),'#skF_3'(k1_wellord2(A_19)))
      | ~ r1_tarski(k1_wellord2(A_19),k1_wellord2(A_19))
      | ~ v1_relat_1(k1_wellord2(A_19))
      | v8_relat_2(k1_wellord2(A_19)) ) ),
    inference(resolution,[status(thm)],[c_94,c_672])).

tff(c_695,plain,(
    ! [A_170] :
      ( r1_tarski('#skF_2'(k1_wellord2(A_170)),'#skF_3'(k1_wellord2(A_170)))
      | v8_relat_2(k1_wellord2(A_170)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_682])).

tff(c_64,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [A_53,B_54,B_55] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_55)
      | ~ r1_tarski(A_53,B_55)
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_142,plain,(
    ! [A_53,B_54,B_2,B_55] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_2)
      | ~ r1_tarski(B_55,B_2)
      | ~ r1_tarski(A_53,B_55)
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_780,plain,(
    ! [A_176,B_177,A_178] :
      ( r2_hidden('#skF_1'(A_176,B_177),'#skF_3'(k1_wellord2(A_178)))
      | ~ r1_tarski(A_176,'#skF_2'(k1_wellord2(A_178)))
      | r1_tarski(A_176,B_177)
      | v8_relat_2(k1_wellord2(A_178)) ) ),
    inference(resolution,[status(thm)],[c_695,c_142])).

tff(c_787,plain,(
    ! [A_176,B_177,B_2,A_178] :
      ( r2_hidden('#skF_1'(A_176,B_177),B_2)
      | ~ r1_tarski('#skF_3'(k1_wellord2(A_178)),B_2)
      | ~ r1_tarski(A_176,'#skF_2'(k1_wellord2(A_178)))
      | r1_tarski(A_176,B_177)
      | v8_relat_2(k1_wellord2(A_178)) ) ),
    inference(resolution,[status(thm)],[c_780,c_2])).

tff(c_1297,plain,(
    ! [A_247,B_248,A_249] :
      ( r2_hidden('#skF_1'(A_247,B_248),'#skF_4'(k1_wellord2(A_249)))
      | ~ r1_tarski(A_247,'#skF_2'(k1_wellord2(A_249)))
      | r1_tarski(A_247,B_248)
      | v8_relat_2(k1_wellord2(A_249)) ) ),
    inference(resolution,[status(thm)],[c_1095,c_787])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1306,plain,(
    ! [A_250,A_251] :
      ( ~ r1_tarski(A_250,'#skF_2'(k1_wellord2(A_251)))
      | r1_tarski(A_250,'#skF_4'(k1_wellord2(A_251)))
      | v8_relat_2(k1_wellord2(A_251)) ) ),
    inference(resolution,[status(thm)],[c_1297,c_4])).

tff(c_1312,plain,(
    ! [A_252] :
      ( r1_tarski('#skF_2'(k1_wellord2(A_252)),'#skF_4'(k1_wellord2(A_252)))
      | v8_relat_2(k1_wellord2(A_252)) ) ),
    inference(resolution,[status(thm)],[c_63,c_1306])).

tff(c_34,plain,(
    ! [C_25,D_26,A_19] :
      ( r2_hidden(k4_tarski(C_25,D_26),k1_wellord2(A_19))
      | ~ r1_tarski(C_25,D_26)
      | ~ r2_hidden(D_26,A_19)
      | ~ r2_hidden(C_25,A_19)
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_263,plain,(
    ! [C_90,D_91,A_92] :
      ( r2_hidden(k4_tarski(C_90,D_91),k1_wellord2(A_92))
      | ~ r1_tarski(C_90,D_91)
      | ~ r2_hidden(D_91,A_92)
      | ~ r2_hidden(C_90,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34])).

tff(c_14,plain,(
    ! [A_9] :
      ( ~ r2_hidden(k4_tarski('#skF_2'(A_9),'#skF_4'(A_9)),A_9)
      | v8_relat_2(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_272,plain,(
    ! [A_92] :
      ( v8_relat_2(k1_wellord2(A_92))
      | ~ v1_relat_1(k1_wellord2(A_92))
      | ~ r1_tarski('#skF_2'(k1_wellord2(A_92)),'#skF_4'(k1_wellord2(A_92)))
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_92)),A_92)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_92)),A_92) ) ),
    inference(resolution,[status(thm)],[c_263,c_14])).

tff(c_286,plain,(
    ! [A_92] :
      ( v8_relat_2(k1_wellord2(A_92))
      | ~ r1_tarski('#skF_2'(k1_wellord2(A_92)),'#skF_4'(k1_wellord2(A_92)))
      | ~ r2_hidden('#skF_4'(k1_wellord2(A_92)),A_92)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_92)),A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_272])).

tff(c_1362,plain,(
    ! [A_253] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(A_253)),A_253)
      | ~ r2_hidden('#skF_2'(k1_wellord2(A_253)),A_253)
      | v8_relat_2(k1_wellord2(A_253)) ) ),
    inference(resolution,[status(thm)],[c_1312,c_286])).

tff(c_1382,plain,(
    ! [A_19] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(A_19)),A_19)
      | ~ r1_tarski(k1_wellord2(A_19),k1_wellord2(A_19))
      | v8_relat_2(k1_wellord2(A_19))
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(resolution,[status(thm)],[c_299,c_1362])).

tff(c_1419,plain,(
    ! [A_254] :
      ( ~ r2_hidden('#skF_4'(k1_wellord2(A_254)),A_254)
      | v8_relat_2(k1_wellord2(A_254)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_1382])).

tff(c_1443,plain,(
    ! [A_19] :
      ( ~ r1_tarski(k1_wellord2(A_19),k1_wellord2(A_19))
      | v8_relat_2(k1_wellord2(A_19))
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(resolution,[status(thm)],[c_258,c_1419])).

tff(c_1470,plain,(
    ! [A_19] : v8_relat_2(k1_wellord2(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_63,c_1443])).

tff(c_40,plain,(
    ~ v8_relat_2(k1_wellord2('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:03:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.65  
% 4.18/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.65  %$ r2_hidden > r1_tarski > v8_relat_2 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_wellord2 > #skF_6 > #skF_2 > #skF_4 > #skF_7 > #skF_3 > #skF_1 > #skF_5
% 4.18/1.65  
% 4.18/1.65  %Foreground sorts:
% 4.18/1.65  
% 4.18/1.65  
% 4.18/1.65  %Background operators:
% 4.18/1.65  
% 4.18/1.65  
% 4.18/1.65  %Foreground operators:
% 4.18/1.65  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.18/1.65  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.18/1.65  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.18/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.18/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.18/1.65  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 4.18/1.65  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.18/1.65  tff('#skF_7', type, '#skF_7': $i).
% 4.18/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.65  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 4.18/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.18/1.65  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.18/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.18/1.65  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.18/1.65  
% 4.18/1.67  tff(f_68, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 4.18/1.67  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.18/1.67  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 4.18/1.67  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (v8_relat_2(A) <=> (![B, C, D]: ((r2_hidden(k4_tarski(B, C), A) & r2_hidden(k4_tarski(C, D), A)) => r2_hidden(k4_tarski(B, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l2_wellord1)).
% 4.18/1.67  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 4.18/1.67  tff(f_71, negated_conjecture, ~(![A]: v8_relat_2(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_wellord2)).
% 4.18/1.67  tff(c_38, plain, (![A_27]: (v1_relat_1(k1_wellord2(A_27)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.18/1.67  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.67  tff(c_58, plain, (![A_32, B_33]: (~r2_hidden('#skF_1'(A_32, B_33), B_33) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.67  tff(c_63, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_58])).
% 4.18/1.67  tff(c_32, plain, (![A_19]: (k3_relat_1(k1_wellord2(A_19))=A_19 | ~v1_relat_1(k1_wellord2(A_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.18/1.67  tff(c_46, plain, (![A_19]: (k3_relat_1(k1_wellord2(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 4.18/1.67  tff(c_70, plain, (![A_41]: (r2_hidden(k4_tarski('#skF_3'(A_41), '#skF_4'(A_41)), A_41) | v8_relat_2(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.67  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.67  tff(c_208, plain, (![A_72, B_73]: (r2_hidden(k4_tarski('#skF_3'(A_72), '#skF_4'(A_72)), B_73) | ~r1_tarski(A_72, B_73) | v8_relat_2(A_72) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_70, c_2])).
% 4.18/1.67  tff(c_8, plain, (![B_7, C_8, A_6]: (r2_hidden(B_7, k3_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.18/1.67  tff(c_250, plain, (![A_86, B_87]: (r2_hidden('#skF_4'(A_86), k3_relat_1(B_87)) | ~v1_relat_1(B_87) | ~r1_tarski(A_86, B_87) | v8_relat_2(A_86) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_208, c_8])).
% 4.18/1.67  tff(c_255, plain, (![A_86, A_19]: (r2_hidden('#skF_4'(A_86), A_19) | ~v1_relat_1(k1_wellord2(A_19)) | ~r1_tarski(A_86, k1_wellord2(A_19)) | v8_relat_2(A_86) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_46, c_250])).
% 4.18/1.67  tff(c_258, plain, (![A_86, A_19]: (r2_hidden('#skF_4'(A_86), A_19) | ~r1_tarski(A_86, k1_wellord2(A_19)) | v8_relat_2(A_86) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_255])).
% 4.18/1.67  tff(c_78, plain, (![A_42]: (r2_hidden(k4_tarski('#skF_2'(A_42), '#skF_3'(A_42)), A_42) | v8_relat_2(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.67  tff(c_196, plain, (![A_70, B_71]: (r2_hidden(k4_tarski('#skF_2'(A_70), '#skF_3'(A_70)), B_71) | ~r1_tarski(A_70, B_71) | v8_relat_2(A_70) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_78, c_2])).
% 4.18/1.67  tff(c_10, plain, (![A_6, C_8, B_7]: (r2_hidden(A_6, k3_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.18/1.67  tff(c_291, plain, (![A_93, B_94]: (r2_hidden('#skF_2'(A_93), k3_relat_1(B_94)) | ~v1_relat_1(B_94) | ~r1_tarski(A_93, B_94) | v8_relat_2(A_93) | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_196, c_10])).
% 4.18/1.67  tff(c_296, plain, (![A_93, A_19]: (r2_hidden('#skF_2'(A_93), A_19) | ~v1_relat_1(k1_wellord2(A_19)) | ~r1_tarski(A_93, k1_wellord2(A_19)) | v8_relat_2(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_46, c_291])).
% 4.18/1.67  tff(c_299, plain, (![A_93, A_19]: (r2_hidden('#skF_2'(A_93), A_19) | ~r1_tarski(A_93, k1_wellord2(A_19)) | v8_relat_2(A_93) | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_296])).
% 4.18/1.67  tff(c_86, plain, (![A_43]: (r2_hidden('#skF_3'(A_43), k3_relat_1(A_43)) | v8_relat_2(A_43) | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_70, c_10])).
% 4.18/1.67  tff(c_91, plain, (![A_19]: (r2_hidden('#skF_3'(k1_wellord2(A_19)), A_19) | v8_relat_2(k1_wellord2(A_19)) | ~v1_relat_1(k1_wellord2(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_86])).
% 4.18/1.67  tff(c_94, plain, (![A_19]: (r2_hidden('#skF_3'(k1_wellord2(A_19)), A_19) | v8_relat_2(k1_wellord2(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_91])).
% 4.18/1.67  tff(c_77, plain, (![A_41, B_2]: (r2_hidden(k4_tarski('#skF_3'(A_41), '#skF_4'(A_41)), B_2) | ~r1_tarski(A_41, B_2) | v8_relat_2(A_41) | ~v1_relat_1(A_41))), inference(resolution, [status(thm)], [c_70, c_2])).
% 4.18/1.67  tff(c_36, plain, (![C_25, D_26, A_19]: (r1_tarski(C_25, D_26) | ~r2_hidden(k4_tarski(C_25, D_26), k1_wellord2(A_19)) | ~r2_hidden(D_26, A_19) | ~r2_hidden(C_25, A_19) | ~v1_relat_1(k1_wellord2(A_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.18/1.67  tff(c_334, plain, (![C_107, D_108, A_109]: (r1_tarski(C_107, D_108) | ~r2_hidden(k4_tarski(C_107, D_108), k1_wellord2(A_109)) | ~r2_hidden(D_108, A_109) | ~r2_hidden(C_107, A_109))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 4.18/1.67  tff(c_978, plain, (![A_210, A_211]: (r1_tarski('#skF_3'(A_210), '#skF_4'(A_210)) | ~r2_hidden('#skF_4'(A_210), A_211) | ~r2_hidden('#skF_3'(A_210), A_211) | ~r1_tarski(A_210, k1_wellord2(A_211)) | v8_relat_2(A_210) | ~v1_relat_1(A_210))), inference(resolution, [status(thm)], [c_77, c_334])).
% 4.18/1.67  tff(c_1061, plain, (![A_213, A_214]: (r1_tarski('#skF_3'(A_213), '#skF_4'(A_213)) | ~r2_hidden('#skF_3'(A_213), A_214) | ~r1_tarski(A_213, k1_wellord2(A_214)) | v8_relat_2(A_213) | ~v1_relat_1(A_213))), inference(resolution, [status(thm)], [c_258, c_978])).
% 4.18/1.67  tff(c_1077, plain, (![A_19]: (r1_tarski('#skF_3'(k1_wellord2(A_19)), '#skF_4'(k1_wellord2(A_19))) | ~r1_tarski(k1_wellord2(A_19), k1_wellord2(A_19)) | ~v1_relat_1(k1_wellord2(A_19)) | v8_relat_2(k1_wellord2(A_19)))), inference(resolution, [status(thm)], [c_94, c_1061])).
% 4.18/1.67  tff(c_1095, plain, (![A_215]: (r1_tarski('#skF_3'(k1_wellord2(A_215)), '#skF_4'(k1_wellord2(A_215))) | v8_relat_2(k1_wellord2(A_215)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_1077])).
% 4.18/1.67  tff(c_85, plain, (![A_42, B_2]: (r2_hidden(k4_tarski('#skF_2'(A_42), '#skF_3'(A_42)), B_2) | ~r1_tarski(A_42, B_2) | v8_relat_2(A_42) | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_78, c_2])).
% 4.18/1.67  tff(c_576, plain, (![A_161, A_162]: (r1_tarski('#skF_2'(A_161), '#skF_3'(A_161)) | ~r2_hidden('#skF_3'(A_161), A_162) | ~r2_hidden('#skF_2'(A_161), A_162) | ~r1_tarski(A_161, k1_wellord2(A_162)) | v8_relat_2(A_161) | ~v1_relat_1(A_161))), inference(resolution, [status(thm)], [c_85, c_334])).
% 4.18/1.67  tff(c_672, plain, (![A_168, A_169]: (r1_tarski('#skF_2'(A_168), '#skF_3'(A_168)) | ~r2_hidden('#skF_3'(A_168), A_169) | ~r1_tarski(A_168, k1_wellord2(A_169)) | v8_relat_2(A_168) | ~v1_relat_1(A_168))), inference(resolution, [status(thm)], [c_299, c_576])).
% 4.18/1.67  tff(c_682, plain, (![A_19]: (r1_tarski('#skF_2'(k1_wellord2(A_19)), '#skF_3'(k1_wellord2(A_19))) | ~r1_tarski(k1_wellord2(A_19), k1_wellord2(A_19)) | ~v1_relat_1(k1_wellord2(A_19)) | v8_relat_2(k1_wellord2(A_19)))), inference(resolution, [status(thm)], [c_94, c_672])).
% 4.18/1.67  tff(c_695, plain, (![A_170]: (r1_tarski('#skF_2'(k1_wellord2(A_170)), '#skF_3'(k1_wellord2(A_170))) | v8_relat_2(k1_wellord2(A_170)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_682])).
% 4.18/1.67  tff(c_64, plain, (![C_34, B_35, A_36]: (r2_hidden(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.67  tff(c_135, plain, (![A_53, B_54, B_55]: (r2_hidden('#skF_1'(A_53, B_54), B_55) | ~r1_tarski(A_53, B_55) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_6, c_64])).
% 4.18/1.67  tff(c_142, plain, (![A_53, B_54, B_2, B_55]: (r2_hidden('#skF_1'(A_53, B_54), B_2) | ~r1_tarski(B_55, B_2) | ~r1_tarski(A_53, B_55) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_135, c_2])).
% 4.18/1.67  tff(c_780, plain, (![A_176, B_177, A_178]: (r2_hidden('#skF_1'(A_176, B_177), '#skF_3'(k1_wellord2(A_178))) | ~r1_tarski(A_176, '#skF_2'(k1_wellord2(A_178))) | r1_tarski(A_176, B_177) | v8_relat_2(k1_wellord2(A_178)))), inference(resolution, [status(thm)], [c_695, c_142])).
% 4.18/1.67  tff(c_787, plain, (![A_176, B_177, B_2, A_178]: (r2_hidden('#skF_1'(A_176, B_177), B_2) | ~r1_tarski('#skF_3'(k1_wellord2(A_178)), B_2) | ~r1_tarski(A_176, '#skF_2'(k1_wellord2(A_178))) | r1_tarski(A_176, B_177) | v8_relat_2(k1_wellord2(A_178)))), inference(resolution, [status(thm)], [c_780, c_2])).
% 4.18/1.67  tff(c_1297, plain, (![A_247, B_248, A_249]: (r2_hidden('#skF_1'(A_247, B_248), '#skF_4'(k1_wellord2(A_249))) | ~r1_tarski(A_247, '#skF_2'(k1_wellord2(A_249))) | r1_tarski(A_247, B_248) | v8_relat_2(k1_wellord2(A_249)))), inference(resolution, [status(thm)], [c_1095, c_787])).
% 4.18/1.67  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.67  tff(c_1306, plain, (![A_250, A_251]: (~r1_tarski(A_250, '#skF_2'(k1_wellord2(A_251))) | r1_tarski(A_250, '#skF_4'(k1_wellord2(A_251))) | v8_relat_2(k1_wellord2(A_251)))), inference(resolution, [status(thm)], [c_1297, c_4])).
% 4.18/1.67  tff(c_1312, plain, (![A_252]: (r1_tarski('#skF_2'(k1_wellord2(A_252)), '#skF_4'(k1_wellord2(A_252))) | v8_relat_2(k1_wellord2(A_252)))), inference(resolution, [status(thm)], [c_63, c_1306])).
% 4.18/1.67  tff(c_34, plain, (![C_25, D_26, A_19]: (r2_hidden(k4_tarski(C_25, D_26), k1_wellord2(A_19)) | ~r1_tarski(C_25, D_26) | ~r2_hidden(D_26, A_19) | ~r2_hidden(C_25, A_19) | ~v1_relat_1(k1_wellord2(A_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.18/1.67  tff(c_263, plain, (![C_90, D_91, A_92]: (r2_hidden(k4_tarski(C_90, D_91), k1_wellord2(A_92)) | ~r1_tarski(C_90, D_91) | ~r2_hidden(D_91, A_92) | ~r2_hidden(C_90, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34])).
% 4.18/1.67  tff(c_14, plain, (![A_9]: (~r2_hidden(k4_tarski('#skF_2'(A_9), '#skF_4'(A_9)), A_9) | v8_relat_2(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.67  tff(c_272, plain, (![A_92]: (v8_relat_2(k1_wellord2(A_92)) | ~v1_relat_1(k1_wellord2(A_92)) | ~r1_tarski('#skF_2'(k1_wellord2(A_92)), '#skF_4'(k1_wellord2(A_92))) | ~r2_hidden('#skF_4'(k1_wellord2(A_92)), A_92) | ~r2_hidden('#skF_2'(k1_wellord2(A_92)), A_92))), inference(resolution, [status(thm)], [c_263, c_14])).
% 4.18/1.67  tff(c_286, plain, (![A_92]: (v8_relat_2(k1_wellord2(A_92)) | ~r1_tarski('#skF_2'(k1_wellord2(A_92)), '#skF_4'(k1_wellord2(A_92))) | ~r2_hidden('#skF_4'(k1_wellord2(A_92)), A_92) | ~r2_hidden('#skF_2'(k1_wellord2(A_92)), A_92))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_272])).
% 4.18/1.67  tff(c_1362, plain, (![A_253]: (~r2_hidden('#skF_4'(k1_wellord2(A_253)), A_253) | ~r2_hidden('#skF_2'(k1_wellord2(A_253)), A_253) | v8_relat_2(k1_wellord2(A_253)))), inference(resolution, [status(thm)], [c_1312, c_286])).
% 4.18/1.67  tff(c_1382, plain, (![A_19]: (~r2_hidden('#skF_4'(k1_wellord2(A_19)), A_19) | ~r1_tarski(k1_wellord2(A_19), k1_wellord2(A_19)) | v8_relat_2(k1_wellord2(A_19)) | ~v1_relat_1(k1_wellord2(A_19)))), inference(resolution, [status(thm)], [c_299, c_1362])).
% 4.18/1.67  tff(c_1419, plain, (![A_254]: (~r2_hidden('#skF_4'(k1_wellord2(A_254)), A_254) | v8_relat_2(k1_wellord2(A_254)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_1382])).
% 4.18/1.67  tff(c_1443, plain, (![A_19]: (~r1_tarski(k1_wellord2(A_19), k1_wellord2(A_19)) | v8_relat_2(k1_wellord2(A_19)) | ~v1_relat_1(k1_wellord2(A_19)))), inference(resolution, [status(thm)], [c_258, c_1419])).
% 4.18/1.67  tff(c_1470, plain, (![A_19]: (v8_relat_2(k1_wellord2(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_63, c_1443])).
% 4.18/1.67  tff(c_40, plain, (~v8_relat_2(k1_wellord2('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.18/1.67  tff(c_1593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1470, c_40])).
% 4.18/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.67  
% 4.18/1.67  Inference rules
% 4.18/1.67  ----------------------
% 4.18/1.67  #Ref     : 0
% 4.18/1.67  #Sup     : 377
% 4.18/1.67  #Fact    : 0
% 4.18/1.67  #Define  : 0
% 4.18/1.67  #Split   : 0
% 4.18/1.67  #Chain   : 0
% 4.18/1.67  #Close   : 0
% 4.18/1.67  
% 4.18/1.67  Ordering : KBO
% 4.18/1.67  
% 4.18/1.67  Simplification rules
% 4.18/1.67  ----------------------
% 4.18/1.67  #Subsume      : 58
% 4.18/1.67  #Demod        : 222
% 4.18/1.67  #Tautology    : 76
% 4.18/1.67  #SimpNegUnit  : 0
% 4.18/1.67  #BackRed      : 3
% 4.18/1.67  
% 4.18/1.67  #Partial instantiations: 0
% 4.18/1.67  #Strategies tried      : 1
% 4.18/1.67  
% 4.18/1.67  Timing (in seconds)
% 4.18/1.67  ----------------------
% 4.18/1.68  Preprocessing        : 0.27
% 4.18/1.68  Parsing              : 0.14
% 4.18/1.68  CNF conversion       : 0.02
% 4.18/1.68  Main loop            : 0.70
% 4.18/1.68  Inferencing          : 0.23
% 4.18/1.68  Reduction            : 0.17
% 4.18/1.68  Demodulation         : 0.11
% 4.18/1.68  BG Simplification    : 0.03
% 4.18/1.68  Subsumption          : 0.22
% 4.18/1.68  Abstraction          : 0.03
% 4.18/1.68  MUC search           : 0.00
% 4.18/1.68  Cooper               : 0.00
% 4.18/1.68  Total                : 1.00
% 4.18/1.68  Index Insertion      : 0.00
% 4.18/1.68  Index Deletion       : 0.00
% 4.18/1.68  Index Matching       : 0.00
% 4.18/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
