%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0507+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:25 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 614 expanded)
%              Number of leaves         :   21 ( 214 expanded)
%              Depth                    :   16
%              Number of atoms          :  220 (2220 expanded)
%              Number of equality atoms :   13 ( 168 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k7_relat_1(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ~ r1_tarski(k7_relat_1('#skF_8','#skF_7'),k7_relat_1('#skF_9','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_20,B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_20)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [D_58,E_59,A_60,B_61] :
      ( r2_hidden(k4_tarski(D_58,E_59),A_60)
      | ~ r2_hidden(k4_tarski(D_58,E_59),k7_relat_1(A_60,B_61))
      | ~ v1_relat_1(k7_relat_1(A_60,B_61))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_223,plain,(
    ! [A_99,B_100,B_101] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_99,B_100),B_101),'#skF_6'(k7_relat_1(A_99,B_100),B_101)),A_99)
      | ~ v1_relat_1(A_99)
      | r1_tarski(k7_relat_1(A_99,B_100),B_101)
      | ~ v1_relat_1(k7_relat_1(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_20,plain,(
    ! [C_35,D_36,B_30,A_20] :
      ( r2_hidden(k4_tarski(C_35,D_36),B_30)
      | ~ r2_hidden(k4_tarski(C_35,D_36),A_20)
      | ~ r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_311,plain,(
    ! [A_120,B_121,B_122,B_123] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_120,B_121),B_122),'#skF_6'(k7_relat_1(A_120,B_121),B_122)),B_123)
      | ~ r1_tarski(A_120,B_123)
      | ~ v1_relat_1(A_120)
      | r1_tarski(k7_relat_1(A_120,B_121),B_122)
      | ~ v1_relat_1(k7_relat_1(A_120,B_121)) ) ),
    inference(resolution,[status(thm)],[c_223,c_20])).

tff(c_22,plain,(
    ! [A_20,B_30] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_30)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_333,plain,(
    ! [A_124,B_125,B_126] :
      ( ~ r1_tarski(A_124,B_125)
      | ~ v1_relat_1(A_124)
      | r1_tarski(k7_relat_1(A_124,B_126),B_125)
      | ~ v1_relat_1(k7_relat_1(A_124,B_126)) ) ),
    inference(resolution,[status(thm)],[c_311,c_22])).

tff(c_350,plain,
    ( ~ r1_tarski('#skF_8',k7_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_333,c_28])).

tff(c_359,plain,
    ( ~ r1_tarski('#skF_8',k7_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_350])).

tff(c_371,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_374,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_371])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_374])).

tff(c_380,plain,(
    v1_relat_1(k7_relat_1('#skF_8','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_241,plain,(
    ! [A_99,B_100] :
      ( ~ v1_relat_1(A_99)
      | r1_tarski(k7_relat_1(A_99,B_100),A_99)
      | ~ v1_relat_1(k7_relat_1(A_99,B_100)) ) ),
    inference(resolution,[status(thm)],[c_223,c_22])).

tff(c_10,plain,(
    ! [A_1,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_12,C_13),'#skF_2'(A_1,B_12,C_13)),A_1)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_12,C_13),'#skF_4'(A_1,B_12,C_13)),C_13)
      | k7_relat_1(A_1,B_12) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_360,plain,(
    ! [A_127,B_128,C_129] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_127,B_128,C_129),'#skF_2'(A_127,B_128,C_129)),C_129)
      | r2_hidden(k4_tarski('#skF_3'(A_127,B_128,C_129),'#skF_4'(A_127,B_128,C_129)),C_129)
      | k7_relat_1(A_127,B_128) = C_129
      | ~ v1_relat_1(C_129)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_381,plain,(
    ! [A_130,B_131] :
      ( r2_hidden(k4_tarski('#skF_3'(A_130,B_131,A_130),'#skF_4'(A_130,B_131,A_130)),A_130)
      | k7_relat_1(A_130,B_131) = A_130
      | ~ v1_relat_1(A_130) ) ),
    inference(resolution,[status(thm)],[c_10,c_360])).

tff(c_18,plain,(
    ! [D_18,B_12,E_19,A_1] :
      ( r2_hidden(D_18,B_12)
      | ~ r2_hidden(k4_tarski(D_18,E_19),k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_396,plain,(
    ! [A_1,B_12,B_131] :
      ( r2_hidden('#skF_3'(k7_relat_1(A_1,B_12),B_131,k7_relat_1(A_1,B_12)),B_12)
      | ~ v1_relat_1(A_1)
      | k7_relat_1(k7_relat_1(A_1,B_12),B_131) = k7_relat_1(A_1,B_12)
      | ~ v1_relat_1(k7_relat_1(A_1,B_12)) ) ),
    inference(resolution,[status(thm)],[c_381,c_18])).

tff(c_369,plain,(
    ! [A_1,B_12] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1,B_12,A_1),'#skF_4'(A_1,B_12,A_1)),A_1)
      | k7_relat_1(A_1,B_12) = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_360])).

tff(c_4,plain,(
    ! [A_1,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_12,C_13),'#skF_2'(A_1,B_12,C_13)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_12,C_13),'#skF_4'(A_1,B_12,C_13)),A_1)
      | ~ r2_hidden('#skF_3'(A_1,B_12,C_13),B_12)
      | k7_relat_1(A_1,B_12) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_688,plain,(
    ! [A_194,B_195,C_196] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_194,B_195,C_196),'#skF_2'(A_194,B_195,C_196)),C_196)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_194,B_195,C_196),'#skF_4'(A_194,B_195,C_196)),A_194)
      | ~ r2_hidden('#skF_3'(A_194,B_195,C_196),B_195)
      | k7_relat_1(A_194,B_195) = C_196
      | ~ v1_relat_1(C_196)
      | ~ v1_relat_1(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_701,plain,(
    ! [A_197,B_198] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_197,B_198,A_197),'#skF_4'(A_197,B_198,A_197)),A_197)
      | ~ r2_hidden('#skF_3'(A_197,B_198,A_197),B_198)
      | k7_relat_1(A_197,B_198) = A_197
      | ~ v1_relat_1(A_197) ) ),
    inference(resolution,[status(thm)],[c_4,c_688])).

tff(c_740,plain,(
    ! [A_199,B_200] :
      ( ~ r2_hidden('#skF_3'(A_199,B_200,A_199),B_200)
      | k7_relat_1(A_199,B_200) = A_199
      | ~ v1_relat_1(A_199) ) ),
    inference(resolution,[status(thm)],[c_369,c_701])).

tff(c_746,plain,(
    ! [A_201,B_202] :
      ( ~ v1_relat_1(A_201)
      | k7_relat_1(k7_relat_1(A_201,B_202),B_202) = k7_relat_1(A_201,B_202)
      | ~ v1_relat_1(k7_relat_1(A_201,B_202)) ) ),
    inference(resolution,[status(thm)],[c_396,c_740])).

tff(c_748,plain,
    ( ~ v1_relat_1('#skF_8')
    | k7_relat_1(k7_relat_1('#skF_8','#skF_7'),'#skF_7') = k7_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_380,c_746])).

tff(c_753,plain,(
    k7_relat_1(k7_relat_1('#skF_8','#skF_7'),'#skF_7') = k7_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_748])).

tff(c_242,plain,(
    ! [A_102,B_103] :
      ( ~ v1_relat_1(A_102)
      | r1_tarski(k7_relat_1(A_102,B_103),A_102)
      | ~ v1_relat_1(k7_relat_1(A_102,B_103)) ) ),
    inference(resolution,[status(thm)],[c_223,c_22])).

tff(c_30,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    ! [C_47,D_48,B_49,A_50] :
      ( r2_hidden(k4_tarski(C_47,D_48),B_49)
      | ~ r2_hidden(k4_tarski(C_47,D_48),A_50)
      | ~ r1_tarski(A_50,B_49)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden(k4_tarski('#skF_5'(A_55,B_56),'#skF_6'(A_55,B_56)),B_57)
      | ~ r1_tarski(A_55,B_57)
      | r1_tarski(A_55,B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_116,plain,(
    ! [A_76,B_77,B_78,B_79] :
      ( r2_hidden(k4_tarski('#skF_5'(A_76,B_77),'#skF_6'(A_76,B_77)),B_78)
      | ~ r1_tarski(B_79,B_78)
      | ~ v1_relat_1(B_79)
      | ~ r1_tarski(A_76,B_79)
      | r1_tarski(A_76,B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_54,c_20])).

tff(c_120,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski('#skF_5'(A_76,B_77),'#skF_6'(A_76,B_77)),'#skF_9')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(A_76,'#skF_8')
      | r1_tarski(A_76,B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_125,plain,(
    ! [A_80,B_81] :
      ( r2_hidden(k4_tarski('#skF_5'(A_80,B_81),'#skF_6'(A_80,B_81)),'#skF_9')
      | ~ r1_tarski(A_80,'#skF_8')
      | r1_tarski(A_80,B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_120])).

tff(c_136,plain,(
    ! [A_82] :
      ( ~ r1_tarski(A_82,'#skF_8')
      | r1_tarski(A_82,'#skF_9')
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_125,c_22])).

tff(c_66,plain,(
    ! [A_55,B_56,B_30,B_57] :
      ( r2_hidden(k4_tarski('#skF_5'(A_55,B_56),'#skF_6'(A_55,B_56)),B_30)
      | ~ r1_tarski(B_57,B_30)
      | ~ v1_relat_1(B_57)
      | ~ r1_tarski(A_55,B_57)
      | r1_tarski(A_55,B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(resolution,[status(thm)],[c_54,c_20])).

tff(c_139,plain,(
    ! [A_55,B_56,A_82] :
      ( r2_hidden(k4_tarski('#skF_5'(A_55,B_56),'#skF_6'(A_55,B_56)),'#skF_9')
      | ~ r1_tarski(A_55,A_82)
      | r1_tarski(A_55,B_56)
      | ~ v1_relat_1(A_55)
      | ~ r1_tarski(A_82,'#skF_8')
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_136,c_66])).

tff(c_452,plain,(
    ! [A_147,B_148,B_149] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_147,B_148),B_149),'#skF_6'(k7_relat_1(A_147,B_148),B_149)),'#skF_9')
      | r1_tarski(k7_relat_1(A_147,B_148),B_149)
      | ~ r1_tarski(A_147,'#skF_8')
      | ~ v1_relat_1(A_147)
      | ~ v1_relat_1(k7_relat_1(A_147,B_148)) ) ),
    inference(resolution,[status(thm)],[c_242,c_139])).

tff(c_467,plain,(
    ! [A_147,B_148] :
      ( r1_tarski(k7_relat_1(A_147,B_148),'#skF_9')
      | ~ r1_tarski(A_147,'#skF_8')
      | ~ v1_relat_1(A_147)
      | ~ v1_relat_1(k7_relat_1(A_147,B_148)) ) ),
    inference(resolution,[status(thm)],[c_452,c_22])).

tff(c_772,plain,
    ( r1_tarski(k7_relat_1('#skF_8','#skF_7'),'#skF_9')
    | ~ r1_tarski(k7_relat_1('#skF_8','#skF_7'),'#skF_8')
    | ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_8','#skF_7'),'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_467])).

tff(c_843,plain,
    ( r1_tarski(k7_relat_1('#skF_8','#skF_7'),'#skF_9')
    | ~ r1_tarski(k7_relat_1('#skF_8','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_753,c_380,c_772])).

tff(c_1126,plain,(
    ~ r1_tarski(k7_relat_1('#skF_8','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_843])).

tff(c_1132,plain,
    ( ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_241,c_1126])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_34,c_1132])).

tff(c_1141,plain,(
    r1_tarski(k7_relat_1('#skF_8','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_48,plain,(
    ! [D_51,B_52,E_53,A_54] :
      ( r2_hidden(D_51,B_52)
      | ~ r2_hidden(k4_tarski(D_51,E_53),k7_relat_1(A_54,B_52))
      | ~ v1_relat_1(k7_relat_1(A_54,B_52))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_53,plain,(
    ! [A_54,B_52,B_30] :
      ( r2_hidden('#skF_5'(k7_relat_1(A_54,B_52),B_30),B_52)
      | ~ v1_relat_1(A_54)
      | r1_tarski(k7_relat_1(A_54,B_52),B_30)
      | ~ v1_relat_1(k7_relat_1(A_54,B_52)) ) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_818,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_5'(k7_relat_1('#skF_8','#skF_7'),B_30),'#skF_7')
      | ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7'))
      | r1_tarski(k7_relat_1(k7_relat_1('#skF_8','#skF_7'),'#skF_7'),B_30)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_8','#skF_7'),'#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_53])).

tff(c_877,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_5'(k7_relat_1('#skF_8','#skF_7'),B_30),'#skF_7')
      | r1_tarski(k7_relat_1('#skF_8','#skF_7'),B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_753,c_753,c_380,c_818])).

tff(c_124,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski('#skF_5'(A_76,B_77),'#skF_6'(A_76,B_77)),'#skF_9')
      | ~ r1_tarski(A_76,'#skF_8')
      | r1_tarski(A_76,B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_120])).

tff(c_80,plain,(
    ! [D_65,E_66,A_67,B_68] :
      ( r2_hidden(k4_tarski(D_65,E_66),k7_relat_1(A_67,B_68))
      | ~ r2_hidden(k4_tarski(D_65,E_66),A_67)
      | ~ r2_hidden(D_65,B_68)
      | ~ v1_relat_1(k7_relat_1(A_67,B_68))
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1741,plain,(
    ! [A_236,A_237,B_238] :
      ( r1_tarski(A_236,k7_relat_1(A_237,B_238))
      | ~ v1_relat_1(A_236)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_236,k7_relat_1(A_237,B_238)),'#skF_6'(A_236,k7_relat_1(A_237,B_238))),A_237)
      | ~ r2_hidden('#skF_5'(A_236,k7_relat_1(A_237,B_238)),B_238)
      | ~ v1_relat_1(k7_relat_1(A_237,B_238))
      | ~ v1_relat_1(A_237) ) ),
    inference(resolution,[status(thm)],[c_80,c_22])).

tff(c_1791,plain,(
    ! [A_76,B_238] :
      ( ~ r2_hidden('#skF_5'(A_76,k7_relat_1('#skF_9',B_238)),B_238)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_238))
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_76,'#skF_8')
      | r1_tarski(A_76,k7_relat_1('#skF_9',B_238))
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_124,c_1741])).

tff(c_1965,plain,(
    ! [A_245,B_246] :
      ( ~ r2_hidden('#skF_5'(A_245,k7_relat_1('#skF_9',B_246)),B_246)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_246))
      | ~ r1_tarski(A_245,'#skF_8')
      | r1_tarski(A_245,k7_relat_1('#skF_9',B_246))
      | ~ v1_relat_1(A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1791])).

tff(c_1973,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
    | ~ r1_tarski(k7_relat_1('#skF_8','#skF_7'),'#skF_8')
    | ~ v1_relat_1(k7_relat_1('#skF_8','#skF_7'))
    | r1_tarski(k7_relat_1('#skF_8','#skF_7'),k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_877,c_1965])).

tff(c_1985,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
    | r1_tarski(k7_relat_1('#skF_8','#skF_7'),k7_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_1141,c_1973])).

tff(c_1986,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1985])).

tff(c_1991,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_1986])).

tff(c_1995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1991])).

%------------------------------------------------------------------------------
