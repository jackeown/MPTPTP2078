%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:14 EST 2020

% Result     : Theorem 11.24s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 502 expanded)
%              Number of leaves         :   32 ( 180 expanded)
%              Depth                    :   16
%              Number of atoms          :  190 (1027 expanded)
%              Number of equality atoms :   25 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),k3_xboole_0(A_9,B_10))
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1209,plain,(
    ! [A_128,C_129,B_130] :
      ( r1_xboole_0(A_128,C_129)
      | ~ r1_xboole_0(B_130,C_129)
      | ~ r1_tarski(A_128,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3765,plain,(
    ! [A_265,B_266,A_267] :
      ( r1_xboole_0(A_265,B_266)
      | ~ r1_tarski(A_265,A_267)
      | k4_xboole_0(A_267,B_266) != A_267 ) ),
    inference(resolution,[status(thm)],[c_42,c_1209])).

tff(c_3770,plain,(
    ! [B_269] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),B_269)
      | k4_xboole_0(k1_tarski('#skF_7'),B_269) != k1_tarski('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_62,c_3765])).

tff(c_300,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_24,B_25] : r1_xboole_0(k4_xboole_0(A_24,B_25),B_25) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_73,plain,(
    ! [B_41,A_42] :
      ( r1_xboole_0(B_41,A_42)
      | ~ r1_xboole_0(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [B_25,A_24] : r1_xboole_0(B_25,k4_xboole_0(A_24,B_25)) ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_126,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = A_50
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_143,plain,(
    ! [B_25,A_24] : k4_xboole_0(B_25,k4_xboole_0(A_24,B_25)) = B_25 ),
    inference(resolution,[status(thm)],[c_78,c_126])).

tff(c_313,plain,(
    ! [B_72] : k3_xboole_0(B_72,B_72) = B_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_143])).

tff(c_687,plain,(
    ! [A_88,B_89,C_90] :
      ( ~ r1_xboole_0(A_88,B_89)
      | ~ r2_hidden(C_90,k3_xboole_0(A_88,B_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_690,plain,(
    ! [B_72,C_90] :
      ( ~ r1_xboole_0(B_72,B_72)
      | ~ r2_hidden(C_90,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_687])).

tff(c_3804,plain,(
    ! [C_90] :
      ( ~ r2_hidden(C_90,k3_xboole_0('#skF_4','#skF_5'))
      | k4_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) != k1_tarski('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3770,c_690])).

tff(c_5617,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) != k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3804])).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1423,plain,(
    ! [A_147,B_148] :
      ( r2_hidden('#skF_3'(A_147,B_148),k3_xboole_0(A_147,B_148))
      | r1_xboole_0(A_147,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_782,plain,(
    ! [D_95,A_96,B_97] :
      ( r2_hidden(D_95,A_96)
      | ~ r2_hidden(D_95,k4_xboole_0(A_96,B_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_803,plain,(
    ! [D_95,A_16,B_17] :
      ( r2_hidden(D_95,A_16)
      | ~ r2_hidden(D_95,k3_xboole_0(A_16,B_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_782])).

tff(c_1489,plain,(
    ! [A_152,B_153] :
      ( r2_hidden('#skF_3'(A_152,B_153),A_152)
      | r1_xboole_0(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_1423,c_803])).

tff(c_24,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,k3_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2899,plain,(
    ! [A_218,B_219,B_220] :
      ( ~ r1_xboole_0(A_218,B_219)
      | r1_xboole_0(k3_xboole_0(A_218,B_219),B_220) ) ),
    inference(resolution,[status(thm)],[c_1489,c_24])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2943,plain,(
    ! [B_220,A_218,B_219] :
      ( r1_xboole_0(B_220,k3_xboole_0(A_218,B_219))
      | ~ r1_xboole_0(A_218,B_219) ) ),
    inference(resolution,[status(thm)],[c_2899,c_20])).

tff(c_1837,plain,(
    ! [A_172,C_173,B_174] :
      ( ~ r1_xboole_0(A_172,C_173)
      | ~ r1_xboole_0(A_172,B_174)
      | r1_xboole_0(A_172,k2_xboole_0(B_174,C_173)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [A_18,C_20,B_19] :
      ( r1_xboole_0(A_18,C_20)
      | ~ r1_xboole_0(B_19,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6951,plain,(
    ! [A_352,B_353,C_354,A_355] :
      ( r1_xboole_0(A_352,k2_xboole_0(B_353,C_354))
      | ~ r1_tarski(A_352,A_355)
      | ~ r1_xboole_0(A_355,C_354)
      | ~ r1_xboole_0(A_355,B_353) ) ),
    inference(resolution,[status(thm)],[c_1837,c_30])).

tff(c_7066,plain,(
    ! [B_358,C_359] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k2_xboole_0(B_358,C_359))
      | ~ r1_xboole_0(k1_tarski('#skF_7'),C_359)
      | ~ r1_xboole_0(k1_tarski('#skF_7'),B_358) ) ),
    inference(resolution,[status(thm)],[c_62,c_6951])).

tff(c_820,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_xboole_0(A_100,B_101)
      | ~ r1_xboole_0(A_100,k2_xboole_0(B_101,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_859,plain,(
    ! [A_103,B_104,C_105] : r1_xboole_0(k4_xboole_0(A_103,k2_xboole_0(B_104,C_105)),B_104) ),
    inference(resolution,[status(thm)],[c_38,c_820])).

tff(c_881,plain,(
    ! [B_106,A_107,C_108] : r1_xboole_0(B_106,k4_xboole_0(A_107,k2_xboole_0(B_106,C_108))) ),
    inference(resolution,[status(thm)],[c_859,c_20])).

tff(c_40,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1727,plain,(
    ! [B_167,A_168,C_169] : k4_xboole_0(B_167,k4_xboole_0(A_168,k2_xboole_0(B_167,C_169))) = B_167 ),
    inference(resolution,[status(thm)],[c_881,c_40])).

tff(c_1769,plain,(
    ! [A_168,C_169] : k3_xboole_0(A_168,k2_xboole_0(A_168,C_169)) = A_168 ),
    inference(superposition,[status(thm),theory(equality)],[c_1727,c_28])).

tff(c_2930,plain,(
    ! [A_168,C_169,B_220] :
      ( ~ r1_xboole_0(A_168,k2_xboole_0(A_168,C_169))
      | r1_xboole_0(A_168,B_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1769,c_2899])).

tff(c_7105,plain,(
    ! [B_220,C_359] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),B_220)
      | ~ r1_xboole_0(k1_tarski('#skF_7'),C_359)
      | ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_7066,c_2930])).

tff(c_8501,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7105])).

tff(c_8532,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2943,c_8501])).

tff(c_54,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,k1_tarski(B_37)) = A_36
      | r2_hidden(B_37,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1389,plain,(
    ! [A_144,B_145,A_146] :
      ( r1_xboole_0(A_144,B_145)
      | ~ r1_tarski(A_144,k4_xboole_0(A_146,B_145)) ) ),
    inference(resolution,[status(thm)],[c_38,c_1209])).

tff(c_12730,plain,(
    ! [A_526,B_527,A_528] :
      ( r1_xboole_0(A_526,k1_tarski(B_527))
      | ~ r1_tarski(A_526,A_528)
      | r2_hidden(B_527,A_528) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1389])).

tff(c_13127,plain,(
    ! [B_531] :
      ( r1_xboole_0(k3_xboole_0('#skF_4','#skF_5'),k1_tarski(B_531))
      | r2_hidden(B_531,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_62,c_12730])).

tff(c_1580,plain,(
    ! [D_160,A_161,B_162] :
      ( r2_hidden(D_160,k4_xboole_0(A_161,B_162))
      | r2_hidden(D_160,B_162)
      | ~ r2_hidden(D_160,A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6313,plain,(
    ! [D_336,A_337,B_338] :
      ( r2_hidden(D_336,k3_xboole_0(A_337,B_338))
      | r2_hidden(D_336,k4_xboole_0(A_337,B_338))
      | ~ r2_hidden(D_336,A_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1580])).

tff(c_935,plain,(
    ! [A_118,B_119] : k4_xboole_0(k4_xboole_0(A_118,B_119),B_119) = k4_xboole_0(A_118,B_119) ),
    inference(resolution,[status(thm)],[c_38,c_126])).

tff(c_52,plain,(
    ! [B_37,A_36] :
      ( ~ r2_hidden(B_37,A_36)
      | k4_xboole_0(A_36,k1_tarski(B_37)) != A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1046,plain,(
    ! [B_37,A_118] : ~ r2_hidden(B_37,k4_xboole_0(A_118,k1_tarski(B_37))) ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_52])).

tff(c_12061,plain,(
    ! [D_507,A_508] :
      ( r2_hidden(D_507,k3_xboole_0(A_508,k1_tarski(D_507)))
      | ~ r2_hidden(D_507,A_508) ) ),
    inference(resolution,[status(thm)],[c_6313,c_1046])).

tff(c_12088,plain,(
    ! [A_508,D_507] :
      ( ~ r1_xboole_0(A_508,k1_tarski(D_507))
      | ~ r2_hidden(D_507,A_508) ) ),
    inference(resolution,[status(thm)],[c_12061,c_24])).

tff(c_14358,plain,(
    ! [B_554] :
      ( ~ r2_hidden(B_554,k3_xboole_0('#skF_4','#skF_5'))
      | r2_hidden(B_554,k1_tarski('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_13127,c_12088])).

tff(c_14429,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),k1_tarski('#skF_7'))
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_14358])).

tff(c_14450,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),k1_tarski('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_8532,c_14429])).

tff(c_588,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,k1_tarski(B_81)) = A_80
      | r2_hidden(B_81,A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_615,plain,(
    ! [A_82,B_83] :
      ( r1_xboole_0(A_82,k1_tarski(B_83))
      | r2_hidden(B_83,A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_588,c_38])).

tff(c_622,plain,(
    ! [B_83,A_82] :
      ( r1_xboole_0(k1_tarski(B_83),A_82)
      | r2_hidden(B_83,A_82) ) ),
    inference(resolution,[status(thm)],[c_615,c_20])).

tff(c_12350,plain,(
    ! [A_511,D_512] :
      ( ~ r1_xboole_0(A_511,k1_tarski(D_512))
      | ~ r2_hidden(D_512,A_511) ) ),
    inference(resolution,[status(thm)],[c_12061,c_24])).

tff(c_12497,plain,(
    ! [D_512,B_83] :
      ( ~ r2_hidden(D_512,k1_tarski(B_83))
      | r2_hidden(B_83,k1_tarski(D_512)) ) ),
    inference(resolution,[status(thm)],[c_622,c_12350])).

tff(c_14465,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_3'('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_14450,c_12497])).

tff(c_899,plain,(
    ! [D_111,B_112,A_113] :
      ( ~ r2_hidden(D_111,B_112)
      | ~ r2_hidden(D_111,k4_xboole_0(A_113,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_902,plain,(
    ! [D_111,B_37,A_36] :
      ( ~ r2_hidden(D_111,k1_tarski(B_37))
      | ~ r2_hidden(D_111,A_36)
      | r2_hidden(B_37,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_899])).

tff(c_14607,plain,(
    ! [A_556] :
      ( ~ r2_hidden('#skF_7',A_556)
      | r2_hidden('#skF_3'('#skF_4','#skF_5'),A_556) ) ),
    inference(resolution,[status(thm)],[c_14465,c_902])).

tff(c_58,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_146,plain,(
    k4_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_58,c_126])).

tff(c_929,plain,(
    ! [D_111] :
      ( ~ r2_hidden(D_111,'#skF_5')
      | ~ r2_hidden(D_111,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_899])).

tff(c_14695,plain,
    ( ~ r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_14607,c_929])).

tff(c_14718,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_14695])).

tff(c_8533,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_622,c_8501])).

tff(c_8570,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_8533,c_803])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3864,plain,(
    ! [D_273,A_274,B_275] :
      ( ~ r2_hidden(D_273,k3_xboole_0(A_274,B_275))
      | ~ r2_hidden(D_273,k4_xboole_0(A_274,B_275)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_899])).

tff(c_19421,plain,(
    ! [D_686,A_687,B_688] :
      ( ~ r2_hidden(D_686,k3_xboole_0(A_687,B_688))
      | r2_hidden(D_686,B_688)
      | ~ r2_hidden(D_686,A_687) ) ),
    inference(resolution,[status(thm)],[c_2,c_3864])).

tff(c_19453,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_8533,c_19421])).

tff(c_19540,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8570,c_19453])).

tff(c_19542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14718,c_19540])).

tff(c_19544,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_14695])).

tff(c_19555,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_19544,c_929])).

tff(c_19563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_19555])).

tff(c_19565,plain,(
    r1_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7105])).

tff(c_19570,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_5')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_19565,c_40])).

tff(c_19577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5617,c_19570])).

tff(c_19580,plain,(
    ! [C_689] : ~ r2_hidden(C_689,k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3804])).

tff(c_19610,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_19580])).

tff(c_19621,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_19610,c_20])).

tff(c_79,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_73])).

tff(c_20354,plain,(
    ! [B_700,C_701,A_702] :
      ( r1_xboole_0(k2_xboole_0(B_700,C_701),A_702)
      | ~ r1_xboole_0(A_702,C_701)
      | ~ r1_xboole_0(A_702,B_700) ) ),
    inference(resolution,[status(thm)],[c_1837,c_20])).

tff(c_56,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_20403,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_6')
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_20354,c_56])).

tff(c_20425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19621,c_79,c_20403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:34:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.24/4.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.24/4.40  
% 11.24/4.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.24/4.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 11.24/4.40  
% 11.24/4.40  %Foreground sorts:
% 11.24/4.40  
% 11.24/4.40  
% 11.24/4.40  %Background operators:
% 11.24/4.40  
% 11.24/4.40  
% 11.24/4.40  %Foreground operators:
% 11.24/4.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.24/4.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.24/4.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.24/4.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.24/4.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.24/4.40  tff('#skF_7', type, '#skF_7': $i).
% 11.24/4.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.24/4.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.24/4.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.24/4.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.24/4.40  tff('#skF_5', type, '#skF_5': $i).
% 11.24/4.40  tff('#skF_6', type, '#skF_6': $i).
% 11.24/4.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.24/4.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.24/4.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.24/4.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.24/4.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.24/4.40  tff('#skF_4', type, '#skF_4': $i).
% 11.24/4.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.24/4.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.24/4.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.24/4.40  
% 11.48/4.42  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 11.48/4.42  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 11.48/4.42  tff(f_85, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.48/4.42  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.48/4.42  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.48/4.42  tff(f_81, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.48/4.42  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.48/4.42  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.48/4.42  tff(f_79, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 11.48/4.42  tff(f_98, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 11.48/4.42  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 11.48/4.42  tff(c_22, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), k3_xboole_0(A_9, B_10)) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.48/4.42  tff(c_62, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.48/4.42  tff(c_42, plain, (![A_26, B_27]: (r1_xboole_0(A_26, B_27) | k4_xboole_0(A_26, B_27)!=A_26)), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.48/4.42  tff(c_1209, plain, (![A_128, C_129, B_130]: (r1_xboole_0(A_128, C_129) | ~r1_xboole_0(B_130, C_129) | ~r1_tarski(A_128, B_130))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.48/4.42  tff(c_3765, plain, (![A_265, B_266, A_267]: (r1_xboole_0(A_265, B_266) | ~r1_tarski(A_265, A_267) | k4_xboole_0(A_267, B_266)!=A_267)), inference(resolution, [status(thm)], [c_42, c_1209])).
% 11.48/4.42  tff(c_3770, plain, (![B_269]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), B_269) | k4_xboole_0(k1_tarski('#skF_7'), B_269)!=k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_62, c_3765])).
% 11.48/4.42  tff(c_300, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.48/4.42  tff(c_38, plain, (![A_24, B_25]: (r1_xboole_0(k4_xboole_0(A_24, B_25), B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.48/4.42  tff(c_73, plain, (![B_41, A_42]: (r1_xboole_0(B_41, A_42) | ~r1_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.48/4.42  tff(c_78, plain, (![B_25, A_24]: (r1_xboole_0(B_25, k4_xboole_0(A_24, B_25)))), inference(resolution, [status(thm)], [c_38, c_73])).
% 11.48/4.42  tff(c_126, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=A_50 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.48/4.42  tff(c_143, plain, (![B_25, A_24]: (k4_xboole_0(B_25, k4_xboole_0(A_24, B_25))=B_25)), inference(resolution, [status(thm)], [c_78, c_126])).
% 11.48/4.42  tff(c_313, plain, (![B_72]: (k3_xboole_0(B_72, B_72)=B_72)), inference(superposition, [status(thm), theory('equality')], [c_300, c_143])).
% 11.48/4.42  tff(c_687, plain, (![A_88, B_89, C_90]: (~r1_xboole_0(A_88, B_89) | ~r2_hidden(C_90, k3_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.48/4.42  tff(c_690, plain, (![B_72, C_90]: (~r1_xboole_0(B_72, B_72) | ~r2_hidden(C_90, B_72))), inference(superposition, [status(thm), theory('equality')], [c_313, c_687])).
% 11.48/4.42  tff(c_3804, plain, (![C_90]: (~r2_hidden(C_90, k3_xboole_0('#skF_4', '#skF_5')) | k4_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))!=k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_3770, c_690])).
% 11.48/4.42  tff(c_5617, plain, (k4_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))!=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_3804])).
% 11.48/4.42  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.48/4.42  tff(c_1423, plain, (![A_147, B_148]: (r2_hidden('#skF_3'(A_147, B_148), k3_xboole_0(A_147, B_148)) | r1_xboole_0(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.48/4.42  tff(c_28, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.48/4.42  tff(c_782, plain, (![D_95, A_96, B_97]: (r2_hidden(D_95, A_96) | ~r2_hidden(D_95, k4_xboole_0(A_96, B_97)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.48/4.42  tff(c_803, plain, (![D_95, A_16, B_17]: (r2_hidden(D_95, A_16) | ~r2_hidden(D_95, k3_xboole_0(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_782])).
% 11.48/4.42  tff(c_1489, plain, (![A_152, B_153]: (r2_hidden('#skF_3'(A_152, B_153), A_152) | r1_xboole_0(A_152, B_153))), inference(resolution, [status(thm)], [c_1423, c_803])).
% 11.48/4.42  tff(c_24, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, k3_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.48/4.42  tff(c_2899, plain, (![A_218, B_219, B_220]: (~r1_xboole_0(A_218, B_219) | r1_xboole_0(k3_xboole_0(A_218, B_219), B_220))), inference(resolution, [status(thm)], [c_1489, c_24])).
% 11.48/4.42  tff(c_20, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.48/4.42  tff(c_2943, plain, (![B_220, A_218, B_219]: (r1_xboole_0(B_220, k3_xboole_0(A_218, B_219)) | ~r1_xboole_0(A_218, B_219))), inference(resolution, [status(thm)], [c_2899, c_20])).
% 11.48/4.42  tff(c_1837, plain, (![A_172, C_173, B_174]: (~r1_xboole_0(A_172, C_173) | ~r1_xboole_0(A_172, B_174) | r1_xboole_0(A_172, k2_xboole_0(B_174, C_173)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.48/4.42  tff(c_30, plain, (![A_18, C_20, B_19]: (r1_xboole_0(A_18, C_20) | ~r1_xboole_0(B_19, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.48/4.42  tff(c_6951, plain, (![A_352, B_353, C_354, A_355]: (r1_xboole_0(A_352, k2_xboole_0(B_353, C_354)) | ~r1_tarski(A_352, A_355) | ~r1_xboole_0(A_355, C_354) | ~r1_xboole_0(A_355, B_353))), inference(resolution, [status(thm)], [c_1837, c_30])).
% 11.48/4.42  tff(c_7066, plain, (![B_358, C_359]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k2_xboole_0(B_358, C_359)) | ~r1_xboole_0(k1_tarski('#skF_7'), C_359) | ~r1_xboole_0(k1_tarski('#skF_7'), B_358))), inference(resolution, [status(thm)], [c_62, c_6951])).
% 11.48/4.42  tff(c_820, plain, (![A_100, B_101, C_102]: (r1_xboole_0(A_100, B_101) | ~r1_xboole_0(A_100, k2_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.48/4.42  tff(c_859, plain, (![A_103, B_104, C_105]: (r1_xboole_0(k4_xboole_0(A_103, k2_xboole_0(B_104, C_105)), B_104))), inference(resolution, [status(thm)], [c_38, c_820])).
% 11.48/4.42  tff(c_881, plain, (![B_106, A_107, C_108]: (r1_xboole_0(B_106, k4_xboole_0(A_107, k2_xboole_0(B_106, C_108))))), inference(resolution, [status(thm)], [c_859, c_20])).
% 11.48/4.42  tff(c_40, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.48/4.42  tff(c_1727, plain, (![B_167, A_168, C_169]: (k4_xboole_0(B_167, k4_xboole_0(A_168, k2_xboole_0(B_167, C_169)))=B_167)), inference(resolution, [status(thm)], [c_881, c_40])).
% 11.48/4.42  tff(c_1769, plain, (![A_168, C_169]: (k3_xboole_0(A_168, k2_xboole_0(A_168, C_169))=A_168)), inference(superposition, [status(thm), theory('equality')], [c_1727, c_28])).
% 11.48/4.42  tff(c_2930, plain, (![A_168, C_169, B_220]: (~r1_xboole_0(A_168, k2_xboole_0(A_168, C_169)) | r1_xboole_0(A_168, B_220))), inference(superposition, [status(thm), theory('equality')], [c_1769, c_2899])).
% 11.48/4.42  tff(c_7105, plain, (![B_220, C_359]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), B_220) | ~r1_xboole_0(k1_tarski('#skF_7'), C_359) | ~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_7066, c_2930])).
% 11.48/4.42  tff(c_8501, plain, (~r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_7105])).
% 11.48/4.42  tff(c_8532, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2943, c_8501])).
% 11.48/4.42  tff(c_54, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k1_tarski(B_37))=A_36 | r2_hidden(B_37, A_36))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.48/4.42  tff(c_1389, plain, (![A_144, B_145, A_146]: (r1_xboole_0(A_144, B_145) | ~r1_tarski(A_144, k4_xboole_0(A_146, B_145)))), inference(resolution, [status(thm)], [c_38, c_1209])).
% 11.48/4.42  tff(c_12730, plain, (![A_526, B_527, A_528]: (r1_xboole_0(A_526, k1_tarski(B_527)) | ~r1_tarski(A_526, A_528) | r2_hidden(B_527, A_528))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1389])).
% 11.48/4.42  tff(c_13127, plain, (![B_531]: (r1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'), k1_tarski(B_531)) | r2_hidden(B_531, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_62, c_12730])).
% 11.48/4.42  tff(c_1580, plain, (![D_160, A_161, B_162]: (r2_hidden(D_160, k4_xboole_0(A_161, B_162)) | r2_hidden(D_160, B_162) | ~r2_hidden(D_160, A_161))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.48/4.42  tff(c_6313, plain, (![D_336, A_337, B_338]: (r2_hidden(D_336, k3_xboole_0(A_337, B_338)) | r2_hidden(D_336, k4_xboole_0(A_337, B_338)) | ~r2_hidden(D_336, A_337))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1580])).
% 11.48/4.42  tff(c_935, plain, (![A_118, B_119]: (k4_xboole_0(k4_xboole_0(A_118, B_119), B_119)=k4_xboole_0(A_118, B_119))), inference(resolution, [status(thm)], [c_38, c_126])).
% 11.48/4.42  tff(c_52, plain, (![B_37, A_36]: (~r2_hidden(B_37, A_36) | k4_xboole_0(A_36, k1_tarski(B_37))!=A_36)), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.48/4.42  tff(c_1046, plain, (![B_37, A_118]: (~r2_hidden(B_37, k4_xboole_0(A_118, k1_tarski(B_37))))), inference(superposition, [status(thm), theory('equality')], [c_935, c_52])).
% 11.48/4.42  tff(c_12061, plain, (![D_507, A_508]: (r2_hidden(D_507, k3_xboole_0(A_508, k1_tarski(D_507))) | ~r2_hidden(D_507, A_508))), inference(resolution, [status(thm)], [c_6313, c_1046])).
% 11.48/4.42  tff(c_12088, plain, (![A_508, D_507]: (~r1_xboole_0(A_508, k1_tarski(D_507)) | ~r2_hidden(D_507, A_508))), inference(resolution, [status(thm)], [c_12061, c_24])).
% 11.48/4.42  tff(c_14358, plain, (![B_554]: (~r2_hidden(B_554, k3_xboole_0('#skF_4', '#skF_5')) | r2_hidden(B_554, k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_13127, c_12088])).
% 11.48/4.42  tff(c_14429, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), k1_tarski('#skF_7')) | r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_14358])).
% 11.48/4.42  tff(c_14450, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), k1_tarski('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_8532, c_14429])).
% 11.48/4.42  tff(c_588, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k1_tarski(B_81))=A_80 | r2_hidden(B_81, A_80))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.48/4.42  tff(c_615, plain, (![A_82, B_83]: (r1_xboole_0(A_82, k1_tarski(B_83)) | r2_hidden(B_83, A_82))), inference(superposition, [status(thm), theory('equality')], [c_588, c_38])).
% 11.48/4.42  tff(c_622, plain, (![B_83, A_82]: (r1_xboole_0(k1_tarski(B_83), A_82) | r2_hidden(B_83, A_82))), inference(resolution, [status(thm)], [c_615, c_20])).
% 11.48/4.42  tff(c_12350, plain, (![A_511, D_512]: (~r1_xboole_0(A_511, k1_tarski(D_512)) | ~r2_hidden(D_512, A_511))), inference(resolution, [status(thm)], [c_12061, c_24])).
% 11.48/4.42  tff(c_12497, plain, (![D_512, B_83]: (~r2_hidden(D_512, k1_tarski(B_83)) | r2_hidden(B_83, k1_tarski(D_512)))), inference(resolution, [status(thm)], [c_622, c_12350])).
% 11.48/4.42  tff(c_14465, plain, (r2_hidden('#skF_7', k1_tarski('#skF_3'('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_14450, c_12497])).
% 11.48/4.42  tff(c_899, plain, (![D_111, B_112, A_113]: (~r2_hidden(D_111, B_112) | ~r2_hidden(D_111, k4_xboole_0(A_113, B_112)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.48/4.42  tff(c_902, plain, (![D_111, B_37, A_36]: (~r2_hidden(D_111, k1_tarski(B_37)) | ~r2_hidden(D_111, A_36) | r2_hidden(B_37, A_36))), inference(superposition, [status(thm), theory('equality')], [c_54, c_899])).
% 11.48/4.42  tff(c_14607, plain, (![A_556]: (~r2_hidden('#skF_7', A_556) | r2_hidden('#skF_3'('#skF_4', '#skF_5'), A_556))), inference(resolution, [status(thm)], [c_14465, c_902])).
% 11.48/4.42  tff(c_58, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.48/4.42  tff(c_146, plain, (k4_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_58, c_126])).
% 11.48/4.42  tff(c_929, plain, (![D_111]: (~r2_hidden(D_111, '#skF_5') | ~r2_hidden(D_111, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_899])).
% 11.48/4.42  tff(c_14695, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_14607, c_929])).
% 11.48/4.42  tff(c_14718, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_14695])).
% 11.48/4.42  tff(c_8533, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_622, c_8501])).
% 11.48/4.42  tff(c_8570, plain, (r2_hidden('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_8533, c_803])).
% 11.48/4.42  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.48/4.42  tff(c_26, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.48/4.42  tff(c_3864, plain, (![D_273, A_274, B_275]: (~r2_hidden(D_273, k3_xboole_0(A_274, B_275)) | ~r2_hidden(D_273, k4_xboole_0(A_274, B_275)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_899])).
% 11.48/4.42  tff(c_19421, plain, (![D_686, A_687, B_688]: (~r2_hidden(D_686, k3_xboole_0(A_687, B_688)) | r2_hidden(D_686, B_688) | ~r2_hidden(D_686, A_687))), inference(resolution, [status(thm)], [c_2, c_3864])).
% 11.48/4.42  tff(c_19453, plain, (r2_hidden('#skF_7', '#skF_5') | ~r2_hidden('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_8533, c_19421])).
% 11.48/4.42  tff(c_19540, plain, (r2_hidden('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8570, c_19453])).
% 11.48/4.42  tff(c_19542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14718, c_19540])).
% 11.48/4.42  tff(c_19544, plain, (r2_hidden('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_14695])).
% 11.48/4.42  tff(c_19555, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_19544, c_929])).
% 11.48/4.42  tff(c_19563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_19555])).
% 11.48/4.42  tff(c_19565, plain, (r1_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_7105])).
% 11.48/4.42  tff(c_19570, plain, (k4_xboole_0(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_5'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_19565, c_40])).
% 11.48/4.42  tff(c_19577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5617, c_19570])).
% 11.48/4.42  tff(c_19580, plain, (![C_689]: (~r2_hidden(C_689, k3_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_3804])).
% 11.48/4.42  tff(c_19610, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_19580])).
% 11.48/4.42  tff(c_19621, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_19610, c_20])).
% 11.48/4.42  tff(c_79, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_73])).
% 11.48/4.42  tff(c_20354, plain, (![B_700, C_701, A_702]: (r1_xboole_0(k2_xboole_0(B_700, C_701), A_702) | ~r1_xboole_0(A_702, C_701) | ~r1_xboole_0(A_702, B_700))), inference(resolution, [status(thm)], [c_1837, c_20])).
% 11.48/4.42  tff(c_56, plain, (~r1_xboole_0(k2_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.48/4.42  tff(c_20403, plain, (~r1_xboole_0('#skF_5', '#skF_6') | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_20354, c_56])).
% 11.48/4.42  tff(c_20425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19621, c_79, c_20403])).
% 11.48/4.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.48/4.42  
% 11.48/4.42  Inference rules
% 11.48/4.42  ----------------------
% 11.48/4.42  #Ref     : 1
% 11.48/4.42  #Sup     : 5103
% 11.48/4.42  #Fact    : 0
% 11.48/4.42  #Define  : 0
% 11.48/4.42  #Split   : 26
% 11.48/4.42  #Chain   : 0
% 11.48/4.42  #Close   : 0
% 11.48/4.42  
% 11.48/4.42  Ordering : KBO
% 11.48/4.42  
% 11.48/4.42  Simplification rules
% 11.48/4.42  ----------------------
% 11.48/4.42  #Subsume      : 1224
% 11.48/4.42  #Demod        : 2352
% 11.48/4.42  #Tautology    : 1453
% 11.48/4.42  #SimpNegUnit  : 79
% 11.48/4.42  #BackRed      : 35
% 11.48/4.42  
% 11.48/4.42  #Partial instantiations: 0
% 11.48/4.42  #Strategies tried      : 1
% 11.48/4.42  
% 11.48/4.42  Timing (in seconds)
% 11.48/4.42  ----------------------
% 11.48/4.43  Preprocessing        : 0.34
% 11.48/4.43  Parsing              : 0.18
% 11.48/4.43  CNF conversion       : 0.02
% 11.48/4.43  Main loop            : 3.29
% 11.48/4.43  Inferencing          : 0.79
% 11.48/4.43  Reduction            : 1.27
% 11.48/4.43  Demodulation         : 0.96
% 11.48/4.43  BG Simplification    : 0.09
% 11.48/4.43  Subsumption          : 0.89
% 11.48/4.43  Abstraction          : 0.13
% 11.48/4.43  MUC search           : 0.00
% 11.48/4.43  Cooper               : 0.00
% 11.48/4.43  Total                : 3.67
% 11.48/4.43  Index Insertion      : 0.00
% 11.48/4.43  Index Deletion       : 0.00
% 11.48/4.43  Index Matching       : 0.00
% 11.48/4.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
