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
% DateTime   : Thu Dec  3 10:00:17 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 4.06s
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
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k8_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_8'),k8_relat_1('#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_19,B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),A_19)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [D_57,E_58,B_59,A_60] :
      ( r2_hidden(k4_tarski(D_57,E_58),B_59)
      | ~ r2_hidden(k4_tarski(D_57,E_58),k8_relat_1(A_60,B_59))
      | ~ v1_relat_1(k8_relat_1(A_60,B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_223,plain,(
    ! [A_98,B_99,B_100] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_98,B_99),B_100),'#skF_6'(k8_relat_1(A_98,B_99),B_100)),B_99)
      | ~ v1_relat_1(B_99)
      | r1_tarski(k8_relat_1(A_98,B_99),B_100)
      | ~ v1_relat_1(k8_relat_1(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_20,plain,(
    ! [C_34,D_35,B_29,A_19] :
      ( r2_hidden(k4_tarski(C_34,D_35),B_29)
      | ~ r2_hidden(k4_tarski(C_34,D_35),A_19)
      | ~ r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_311,plain,(
    ! [A_119,B_120,B_121,B_122] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_119,B_120),B_121),'#skF_6'(k8_relat_1(A_119,B_120),B_121)),B_122)
      | ~ r1_tarski(B_120,B_122)
      | ~ v1_relat_1(B_120)
      | r1_tarski(k8_relat_1(A_119,B_120),B_121)
      | ~ v1_relat_1(k8_relat_1(A_119,B_120)) ) ),
    inference(resolution,[status(thm)],[c_223,c_20])).

tff(c_22,plain,(
    ! [A_19,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),B_29)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_333,plain,(
    ! [B_123,B_124,A_125] :
      ( ~ r1_tarski(B_123,B_124)
      | ~ v1_relat_1(B_123)
      | r1_tarski(k8_relat_1(A_125,B_123),B_124)
      | ~ v1_relat_1(k8_relat_1(A_125,B_123)) ) ),
    inference(resolution,[status(thm)],[c_311,c_22])).

tff(c_350,plain,
    ( ~ r1_tarski('#skF_8',k8_relat_1('#skF_7','#skF_9'))
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_333,c_28])).

tff(c_359,plain,
    ( ~ r1_tarski('#skF_8',k8_relat_1('#skF_7','#skF_9'))
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_350])).

tff(c_371,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_374,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_371])).

tff(c_378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_374])).

tff(c_380,plain,(
    v1_relat_1(k8_relat_1('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_241,plain,(
    ! [B_99,A_98] :
      ( ~ v1_relat_1(B_99)
      | r1_tarski(k8_relat_1(A_98,B_99),B_99)
      | ~ v1_relat_1(k8_relat_1(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_223,c_22])).

tff(c_10,plain,(
    ! [A_1,B_2,C_12] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),B_2)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),C_12)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_360,plain,(
    ! [A_126,B_127,C_128] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_126,B_127,C_128),'#skF_2'(A_126,B_127,C_128)),C_128)
      | r2_hidden(k4_tarski('#skF_3'(A_126,B_127,C_128),'#skF_4'(A_126,B_127,C_128)),C_128)
      | k8_relat_1(A_126,B_127) = C_128
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_381,plain,(
    ! [A_129,B_130] :
      ( r2_hidden(k4_tarski('#skF_3'(A_129,B_130,B_130),'#skF_4'(A_129,B_130,B_130)),B_130)
      | k8_relat_1(A_129,B_130) = B_130
      | ~ v1_relat_1(B_130) ) ),
    inference(resolution,[status(thm)],[c_10,c_360])).

tff(c_18,plain,(
    ! [E_18,A_1,D_17,B_2] :
      ( r2_hidden(E_18,A_1)
      | ~ r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_396,plain,(
    ! [A_129,A_1,B_2] :
      ( r2_hidden('#skF_4'(A_129,k8_relat_1(A_1,B_2),k8_relat_1(A_1,B_2)),A_1)
      | ~ v1_relat_1(B_2)
      | k8_relat_1(A_129,k8_relat_1(A_1,B_2)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(k8_relat_1(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_381,c_18])).

tff(c_369,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1,B_2,B_2),'#skF_4'(A_1,B_2,B_2)),B_2)
      | k8_relat_1(A_1,B_2) = B_2
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_10,c_360])).

tff(c_4,plain,(
    ! [A_1,B_2,C_12] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden('#skF_4'(A_1,B_2,C_12),A_1)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_699,plain,(
    ! [A_195,B_196,C_197] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_195,B_196,C_197),'#skF_2'(A_195,B_196,C_197)),C_197)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_195,B_196,C_197),'#skF_4'(A_195,B_196,C_197)),B_196)
      | ~ r2_hidden('#skF_4'(A_195,B_196,C_197),A_195)
      | k8_relat_1(A_195,B_196) = C_197
      | ~ v1_relat_1(C_197)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_712,plain,(
    ! [A_198,B_199] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_198,B_199,B_199),'#skF_4'(A_198,B_199,B_199)),B_199)
      | ~ r2_hidden('#skF_4'(A_198,B_199,B_199),A_198)
      | k8_relat_1(A_198,B_199) = B_199
      | ~ v1_relat_1(B_199) ) ),
    inference(resolution,[status(thm)],[c_4,c_699])).

tff(c_751,plain,(
    ! [A_200,B_201] :
      ( ~ r2_hidden('#skF_4'(A_200,B_201,B_201),A_200)
      | k8_relat_1(A_200,B_201) = B_201
      | ~ v1_relat_1(B_201) ) ),
    inference(resolution,[status(thm)],[c_369,c_712])).

tff(c_757,plain,(
    ! [B_202,A_203] :
      ( ~ v1_relat_1(B_202)
      | k8_relat_1(A_203,k8_relat_1(A_203,B_202)) = k8_relat_1(A_203,B_202)
      | ~ v1_relat_1(k8_relat_1(A_203,B_202)) ) ),
    inference(resolution,[status(thm)],[c_396,c_751])).

tff(c_759,plain,
    ( ~ v1_relat_1('#skF_8')
    | k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_8')) = k8_relat_1('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_380,c_757])).

tff(c_764,plain,(
    k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_8')) = k8_relat_1('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_759])).

tff(c_242,plain,(
    ! [B_101,A_102] :
      ( ~ v1_relat_1(B_101)
      | r1_tarski(k8_relat_1(A_102,B_101),B_101)
      | ~ v1_relat_1(k8_relat_1(A_102,B_101)) ) ),
    inference(resolution,[status(thm)],[c_223,c_22])).

tff(c_30,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ! [C_46,D_47,B_48,A_49] :
      ( r2_hidden(k4_tarski(C_46,D_47),B_48)
      | ~ r2_hidden(k4_tarski(C_46,D_47),A_49)
      | ~ r1_tarski(A_49,B_48)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden(k4_tarski('#skF_5'(A_54,B_55),'#skF_6'(A_54,B_55)),B_56)
      | ~ r1_tarski(A_54,B_56)
      | r1_tarski(A_54,B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_116,plain,(
    ! [A_75,B_76,B_77,B_78] :
      ( r2_hidden(k4_tarski('#skF_5'(A_75,B_76),'#skF_6'(A_75,B_76)),B_77)
      | ~ r1_tarski(B_78,B_77)
      | ~ v1_relat_1(B_78)
      | ~ r1_tarski(A_75,B_78)
      | r1_tarski(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_54,c_20])).

tff(c_120,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(k4_tarski('#skF_5'(A_75,B_76),'#skF_6'(A_75,B_76)),'#skF_9')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(A_75,'#skF_8')
      | r1_tarski(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_125,plain,(
    ! [A_79,B_80] :
      ( r2_hidden(k4_tarski('#skF_5'(A_79,B_80),'#skF_6'(A_79,B_80)),'#skF_9')
      | ~ r1_tarski(A_79,'#skF_8')
      | r1_tarski(A_79,B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_120])).

tff(c_136,plain,(
    ! [A_81] :
      ( ~ r1_tarski(A_81,'#skF_8')
      | r1_tarski(A_81,'#skF_9')
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_125,c_22])).

tff(c_66,plain,(
    ! [A_54,B_55,B_29,B_56] :
      ( r2_hidden(k4_tarski('#skF_5'(A_54,B_55),'#skF_6'(A_54,B_55)),B_29)
      | ~ r1_tarski(B_56,B_29)
      | ~ v1_relat_1(B_56)
      | ~ r1_tarski(A_54,B_56)
      | r1_tarski(A_54,B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_54,c_20])).

tff(c_139,plain,(
    ! [A_54,B_55,A_81] :
      ( r2_hidden(k4_tarski('#skF_5'(A_54,B_55),'#skF_6'(A_54,B_55)),'#skF_9')
      | ~ r1_tarski(A_54,A_81)
      | r1_tarski(A_54,B_55)
      | ~ v1_relat_1(A_54)
      | ~ r1_tarski(A_81,'#skF_8')
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_136,c_66])).

tff(c_457,plain,(
    ! [A_146,B_147,B_148] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_146,B_147),B_148),'#skF_6'(k8_relat_1(A_146,B_147),B_148)),'#skF_9')
      | r1_tarski(k8_relat_1(A_146,B_147),B_148)
      | ~ r1_tarski(B_147,'#skF_8')
      | ~ v1_relat_1(B_147)
      | ~ v1_relat_1(k8_relat_1(A_146,B_147)) ) ),
    inference(resolution,[status(thm)],[c_242,c_139])).

tff(c_472,plain,(
    ! [A_146,B_147] :
      ( r1_tarski(k8_relat_1(A_146,B_147),'#skF_9')
      | ~ r1_tarski(B_147,'#skF_8')
      | ~ v1_relat_1(B_147)
      | ~ v1_relat_1(k8_relat_1(A_146,B_147)) ) ),
    inference(resolution,[status(thm)],[c_457,c_22])).

tff(c_783,plain,
    ( r1_tarski(k8_relat_1('#skF_7','#skF_8'),'#skF_9')
    | ~ r1_tarski(k8_relat_1('#skF_7','#skF_8'),'#skF_8')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8'))
    | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_472])).

tff(c_854,plain,
    ( r1_tarski(k8_relat_1('#skF_7','#skF_8'),'#skF_9')
    | ~ r1_tarski(k8_relat_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_764,c_380,c_783])).

tff(c_1137,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_854])).

tff(c_1143,plain,
    ( ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_241,c_1137])).

tff(c_1150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_34,c_1143])).

tff(c_1152,plain,(
    r1_tarski(k8_relat_1('#skF_7','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_854])).

tff(c_48,plain,(
    ! [E_50,A_51,D_52,B_53] :
      ( r2_hidden(E_50,A_51)
      | ~ r2_hidden(k4_tarski(D_52,E_50),k8_relat_1(A_51,B_53))
      | ~ v1_relat_1(k8_relat_1(A_51,B_53))
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [A_51,B_53,B_29] :
      ( r2_hidden('#skF_6'(k8_relat_1(A_51,B_53),B_29),A_51)
      | ~ v1_relat_1(B_53)
      | r1_tarski(k8_relat_1(A_51,B_53),B_29)
      | ~ v1_relat_1(k8_relat_1(A_51,B_53)) ) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_829,plain,(
    ! [B_29] :
      ( r2_hidden('#skF_6'(k8_relat_1('#skF_7','#skF_8'),B_29),'#skF_7')
      | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8'))
      | r1_tarski(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_8')),B_29)
      | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_8'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_53])).

tff(c_888,plain,(
    ! [B_29] :
      ( r2_hidden('#skF_6'(k8_relat_1('#skF_7','#skF_8'),B_29),'#skF_7')
      | r1_tarski(k8_relat_1('#skF_7','#skF_8'),B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_764,c_764,c_380,c_829])).

tff(c_124,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(k4_tarski('#skF_5'(A_75,B_76),'#skF_6'(A_75,B_76)),'#skF_9')
      | ~ r1_tarski(A_75,'#skF_8')
      | r1_tarski(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_120])).

tff(c_80,plain,(
    ! [D_64,E_65,A_66,B_67] :
      ( r2_hidden(k4_tarski(D_64,E_65),k8_relat_1(A_66,B_67))
      | ~ r2_hidden(k4_tarski(D_64,E_65),B_67)
      | ~ r2_hidden(E_65,A_66)
      | ~ v1_relat_1(k8_relat_1(A_66,B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1282,plain,(
    ! [A_215,A_216,B_217] :
      ( r1_tarski(A_215,k8_relat_1(A_216,B_217))
      | ~ v1_relat_1(A_215)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_215,k8_relat_1(A_216,B_217)),'#skF_6'(A_215,k8_relat_1(A_216,B_217))),B_217)
      | ~ r2_hidden('#skF_6'(A_215,k8_relat_1(A_216,B_217)),A_216)
      | ~ v1_relat_1(k8_relat_1(A_216,B_217))
      | ~ v1_relat_1(B_217) ) ),
    inference(resolution,[status(thm)],[c_80,c_22])).

tff(c_1318,plain,(
    ! [A_75,A_216] :
      ( ~ r2_hidden('#skF_6'(A_75,k8_relat_1(A_216,'#skF_9')),A_216)
      | ~ v1_relat_1(k8_relat_1(A_216,'#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_75,'#skF_8')
      | r1_tarski(A_75,k8_relat_1(A_216,'#skF_9'))
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_124,c_1282])).

tff(c_1415,plain,(
    ! [A_222,A_223] :
      ( ~ r2_hidden('#skF_6'(A_222,k8_relat_1(A_223,'#skF_9')),A_223)
      | ~ v1_relat_1(k8_relat_1(A_223,'#skF_9'))
      | ~ r1_tarski(A_222,'#skF_8')
      | r1_tarski(A_222,k8_relat_1(A_223,'#skF_9'))
      | ~ v1_relat_1(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1318])).

tff(c_1423,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
    | ~ r1_tarski(k8_relat_1('#skF_7','#skF_8'),'#skF_8')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_8'))
    | r1_tarski(k8_relat_1('#skF_7','#skF_8'),k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_888,c_1415])).

tff(c_1435,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
    | r1_tarski(k8_relat_1('#skF_7','#skF_8'),k8_relat_1('#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_1152,c_1423])).

tff(c_1436,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1435])).

tff(c_1441,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_1436])).

tff(c_1445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1441])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:12:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.79  
% 3.94/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.80  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 3.94/1.80  
% 3.94/1.80  %Foreground sorts:
% 3.94/1.80  
% 3.94/1.80  
% 3.94/1.80  %Background operators:
% 3.94/1.80  
% 3.94/1.80  
% 3.94/1.80  %Foreground operators:
% 3.94/1.80  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.94/1.80  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.94/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.94/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.94/1.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.94/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.94/1.80  tff('#skF_7', type, '#skF_7': $i).
% 3.94/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.94/1.80  tff('#skF_9', type, '#skF_9': $i).
% 3.94/1.80  tff('#skF_8', type, '#skF_8': $i).
% 3.94/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.94/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.80  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.94/1.80  
% 4.06/1.82  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 4.06/1.82  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 4.06/1.82  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 4.06/1.82  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 4.06/1.82  tff(c_32, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.06/1.82  tff(c_26, plain, (![A_36, B_37]: (v1_relat_1(k8_relat_1(A_36, B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.06/1.82  tff(c_28, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_8'), k8_relat_1('#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.06/1.82  tff(c_34, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.06/1.82  tff(c_24, plain, (![A_19, B_29]: (r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), A_19) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.82  tff(c_68, plain, (![D_57, E_58, B_59, A_60]: (r2_hidden(k4_tarski(D_57, E_58), B_59) | ~r2_hidden(k4_tarski(D_57, E_58), k8_relat_1(A_60, B_59)) | ~v1_relat_1(k8_relat_1(A_60, B_59)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.82  tff(c_223, plain, (![A_98, B_99, B_100]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_98, B_99), B_100), '#skF_6'(k8_relat_1(A_98, B_99), B_100)), B_99) | ~v1_relat_1(B_99) | r1_tarski(k8_relat_1(A_98, B_99), B_100) | ~v1_relat_1(k8_relat_1(A_98, B_99)))), inference(resolution, [status(thm)], [c_24, c_68])).
% 4.06/1.82  tff(c_20, plain, (![C_34, D_35, B_29, A_19]: (r2_hidden(k4_tarski(C_34, D_35), B_29) | ~r2_hidden(k4_tarski(C_34, D_35), A_19) | ~r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.82  tff(c_311, plain, (![A_119, B_120, B_121, B_122]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_119, B_120), B_121), '#skF_6'(k8_relat_1(A_119, B_120), B_121)), B_122) | ~r1_tarski(B_120, B_122) | ~v1_relat_1(B_120) | r1_tarski(k8_relat_1(A_119, B_120), B_121) | ~v1_relat_1(k8_relat_1(A_119, B_120)))), inference(resolution, [status(thm)], [c_223, c_20])).
% 4.06/1.82  tff(c_22, plain, (![A_19, B_29]: (~r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), B_29) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.82  tff(c_333, plain, (![B_123, B_124, A_125]: (~r1_tarski(B_123, B_124) | ~v1_relat_1(B_123) | r1_tarski(k8_relat_1(A_125, B_123), B_124) | ~v1_relat_1(k8_relat_1(A_125, B_123)))), inference(resolution, [status(thm)], [c_311, c_22])).
% 4.06/1.82  tff(c_350, plain, (~r1_tarski('#skF_8', k8_relat_1('#skF_7', '#skF_9')) | ~v1_relat_1('#skF_8') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_333, c_28])).
% 4.06/1.82  tff(c_359, plain, (~r1_tarski('#skF_8', k8_relat_1('#skF_7', '#skF_9')) | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_350])).
% 4.06/1.82  tff(c_371, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_359])).
% 4.06/1.82  tff(c_374, plain, (~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26, c_371])).
% 4.06/1.82  tff(c_378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_374])).
% 4.06/1.82  tff(c_380, plain, (v1_relat_1(k8_relat_1('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_359])).
% 4.06/1.82  tff(c_241, plain, (![B_99, A_98]: (~v1_relat_1(B_99) | r1_tarski(k8_relat_1(A_98, B_99), B_99) | ~v1_relat_1(k8_relat_1(A_98, B_99)))), inference(resolution, [status(thm)], [c_223, c_22])).
% 4.06/1.82  tff(c_10, plain, (![A_1, B_2, C_12]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), B_2) | r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), C_12) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.82  tff(c_360, plain, (![A_126, B_127, C_128]: (~r2_hidden(k4_tarski('#skF_1'(A_126, B_127, C_128), '#skF_2'(A_126, B_127, C_128)), C_128) | r2_hidden(k4_tarski('#skF_3'(A_126, B_127, C_128), '#skF_4'(A_126, B_127, C_128)), C_128) | k8_relat_1(A_126, B_127)=C_128 | ~v1_relat_1(C_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.82  tff(c_381, plain, (![A_129, B_130]: (r2_hidden(k4_tarski('#skF_3'(A_129, B_130, B_130), '#skF_4'(A_129, B_130, B_130)), B_130) | k8_relat_1(A_129, B_130)=B_130 | ~v1_relat_1(B_130))), inference(resolution, [status(thm)], [c_10, c_360])).
% 4.06/1.82  tff(c_18, plain, (![E_18, A_1, D_17, B_2]: (r2_hidden(E_18, A_1) | ~r2_hidden(k4_tarski(D_17, E_18), k8_relat_1(A_1, B_2)) | ~v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.82  tff(c_396, plain, (![A_129, A_1, B_2]: (r2_hidden('#skF_4'(A_129, k8_relat_1(A_1, B_2), k8_relat_1(A_1, B_2)), A_1) | ~v1_relat_1(B_2) | k8_relat_1(A_129, k8_relat_1(A_1, B_2))=k8_relat_1(A_1, B_2) | ~v1_relat_1(k8_relat_1(A_1, B_2)))), inference(resolution, [status(thm)], [c_381, c_18])).
% 4.06/1.82  tff(c_369, plain, (![A_1, B_2]: (r2_hidden(k4_tarski('#skF_3'(A_1, B_2, B_2), '#skF_4'(A_1, B_2, B_2)), B_2) | k8_relat_1(A_1, B_2)=B_2 | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_10, c_360])).
% 4.06/1.82  tff(c_4, plain, (![A_1, B_2, C_12]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), B_2) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), B_2) | ~r2_hidden('#skF_4'(A_1, B_2, C_12), A_1) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.82  tff(c_699, plain, (![A_195, B_196, C_197]: (~r2_hidden(k4_tarski('#skF_1'(A_195, B_196, C_197), '#skF_2'(A_195, B_196, C_197)), C_197) | ~r2_hidden(k4_tarski('#skF_3'(A_195, B_196, C_197), '#skF_4'(A_195, B_196, C_197)), B_196) | ~r2_hidden('#skF_4'(A_195, B_196, C_197), A_195) | k8_relat_1(A_195, B_196)=C_197 | ~v1_relat_1(C_197) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.82  tff(c_712, plain, (![A_198, B_199]: (~r2_hidden(k4_tarski('#skF_3'(A_198, B_199, B_199), '#skF_4'(A_198, B_199, B_199)), B_199) | ~r2_hidden('#skF_4'(A_198, B_199, B_199), A_198) | k8_relat_1(A_198, B_199)=B_199 | ~v1_relat_1(B_199))), inference(resolution, [status(thm)], [c_4, c_699])).
% 4.06/1.82  tff(c_751, plain, (![A_200, B_201]: (~r2_hidden('#skF_4'(A_200, B_201, B_201), A_200) | k8_relat_1(A_200, B_201)=B_201 | ~v1_relat_1(B_201))), inference(resolution, [status(thm)], [c_369, c_712])).
% 4.06/1.82  tff(c_757, plain, (![B_202, A_203]: (~v1_relat_1(B_202) | k8_relat_1(A_203, k8_relat_1(A_203, B_202))=k8_relat_1(A_203, B_202) | ~v1_relat_1(k8_relat_1(A_203, B_202)))), inference(resolution, [status(thm)], [c_396, c_751])).
% 4.06/1.82  tff(c_759, plain, (~v1_relat_1('#skF_8') | k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_8'))=k8_relat_1('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_380, c_757])).
% 4.06/1.82  tff(c_764, plain, (k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_8'))=k8_relat_1('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_759])).
% 4.06/1.82  tff(c_242, plain, (![B_101, A_102]: (~v1_relat_1(B_101) | r1_tarski(k8_relat_1(A_102, B_101), B_101) | ~v1_relat_1(k8_relat_1(A_102, B_101)))), inference(resolution, [status(thm)], [c_223, c_22])).
% 4.06/1.82  tff(c_30, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.06/1.82  tff(c_44, plain, (![C_46, D_47, B_48, A_49]: (r2_hidden(k4_tarski(C_46, D_47), B_48) | ~r2_hidden(k4_tarski(C_46, D_47), A_49) | ~r1_tarski(A_49, B_48) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.82  tff(c_54, plain, (![A_54, B_55, B_56]: (r2_hidden(k4_tarski('#skF_5'(A_54, B_55), '#skF_6'(A_54, B_55)), B_56) | ~r1_tarski(A_54, B_56) | r1_tarski(A_54, B_55) | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_24, c_44])).
% 4.06/1.82  tff(c_116, plain, (![A_75, B_76, B_77, B_78]: (r2_hidden(k4_tarski('#skF_5'(A_75, B_76), '#skF_6'(A_75, B_76)), B_77) | ~r1_tarski(B_78, B_77) | ~v1_relat_1(B_78) | ~r1_tarski(A_75, B_78) | r1_tarski(A_75, B_76) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_54, c_20])).
% 4.06/1.82  tff(c_120, plain, (![A_75, B_76]: (r2_hidden(k4_tarski('#skF_5'(A_75, B_76), '#skF_6'(A_75, B_76)), '#skF_9') | ~v1_relat_1('#skF_8') | ~r1_tarski(A_75, '#skF_8') | r1_tarski(A_75, B_76) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_30, c_116])).
% 4.06/1.82  tff(c_125, plain, (![A_79, B_80]: (r2_hidden(k4_tarski('#skF_5'(A_79, B_80), '#skF_6'(A_79, B_80)), '#skF_9') | ~r1_tarski(A_79, '#skF_8') | r1_tarski(A_79, B_80) | ~v1_relat_1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_120])).
% 4.06/1.82  tff(c_136, plain, (![A_81]: (~r1_tarski(A_81, '#skF_8') | r1_tarski(A_81, '#skF_9') | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_125, c_22])).
% 4.06/1.82  tff(c_66, plain, (![A_54, B_55, B_29, B_56]: (r2_hidden(k4_tarski('#skF_5'(A_54, B_55), '#skF_6'(A_54, B_55)), B_29) | ~r1_tarski(B_56, B_29) | ~v1_relat_1(B_56) | ~r1_tarski(A_54, B_56) | r1_tarski(A_54, B_55) | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_54, c_20])).
% 4.06/1.82  tff(c_139, plain, (![A_54, B_55, A_81]: (r2_hidden(k4_tarski('#skF_5'(A_54, B_55), '#skF_6'(A_54, B_55)), '#skF_9') | ~r1_tarski(A_54, A_81) | r1_tarski(A_54, B_55) | ~v1_relat_1(A_54) | ~r1_tarski(A_81, '#skF_8') | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_136, c_66])).
% 4.06/1.82  tff(c_457, plain, (![A_146, B_147, B_148]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_146, B_147), B_148), '#skF_6'(k8_relat_1(A_146, B_147), B_148)), '#skF_9') | r1_tarski(k8_relat_1(A_146, B_147), B_148) | ~r1_tarski(B_147, '#skF_8') | ~v1_relat_1(B_147) | ~v1_relat_1(k8_relat_1(A_146, B_147)))), inference(resolution, [status(thm)], [c_242, c_139])).
% 4.06/1.82  tff(c_472, plain, (![A_146, B_147]: (r1_tarski(k8_relat_1(A_146, B_147), '#skF_9') | ~r1_tarski(B_147, '#skF_8') | ~v1_relat_1(B_147) | ~v1_relat_1(k8_relat_1(A_146, B_147)))), inference(resolution, [status(thm)], [c_457, c_22])).
% 4.06/1.82  tff(c_783, plain, (r1_tarski(k8_relat_1('#skF_7', '#skF_8'), '#skF_9') | ~r1_tarski(k8_relat_1('#skF_7', '#skF_8'), '#skF_8') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_8')) | ~v1_relat_1(k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_764, c_472])).
% 4.06/1.82  tff(c_854, plain, (r1_tarski(k8_relat_1('#skF_7', '#skF_8'), '#skF_9') | ~r1_tarski(k8_relat_1('#skF_7', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_764, c_380, c_783])).
% 4.06/1.82  tff(c_1137, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_854])).
% 4.06/1.82  tff(c_1143, plain, (~v1_relat_1('#skF_8') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_241, c_1137])).
% 4.06/1.82  tff(c_1150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_380, c_34, c_1143])).
% 4.06/1.82  tff(c_1152, plain, (r1_tarski(k8_relat_1('#skF_7', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_854])).
% 4.06/1.82  tff(c_48, plain, (![E_50, A_51, D_52, B_53]: (r2_hidden(E_50, A_51) | ~r2_hidden(k4_tarski(D_52, E_50), k8_relat_1(A_51, B_53)) | ~v1_relat_1(k8_relat_1(A_51, B_53)) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.82  tff(c_53, plain, (![A_51, B_53, B_29]: (r2_hidden('#skF_6'(k8_relat_1(A_51, B_53), B_29), A_51) | ~v1_relat_1(B_53) | r1_tarski(k8_relat_1(A_51, B_53), B_29) | ~v1_relat_1(k8_relat_1(A_51, B_53)))), inference(resolution, [status(thm)], [c_24, c_48])).
% 4.06/1.82  tff(c_829, plain, (![B_29]: (r2_hidden('#skF_6'(k8_relat_1('#skF_7', '#skF_8'), B_29), '#skF_7') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_8')) | r1_tarski(k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_8')), B_29) | ~v1_relat_1(k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_8'))))), inference(superposition, [status(thm), theory('equality')], [c_764, c_53])).
% 4.06/1.82  tff(c_888, plain, (![B_29]: (r2_hidden('#skF_6'(k8_relat_1('#skF_7', '#skF_8'), B_29), '#skF_7') | r1_tarski(k8_relat_1('#skF_7', '#skF_8'), B_29))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_764, c_764, c_380, c_829])).
% 4.06/1.82  tff(c_124, plain, (![A_75, B_76]: (r2_hidden(k4_tarski('#skF_5'(A_75, B_76), '#skF_6'(A_75, B_76)), '#skF_9') | ~r1_tarski(A_75, '#skF_8') | r1_tarski(A_75, B_76) | ~v1_relat_1(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_120])).
% 4.06/1.82  tff(c_80, plain, (![D_64, E_65, A_66, B_67]: (r2_hidden(k4_tarski(D_64, E_65), k8_relat_1(A_66, B_67)) | ~r2_hidden(k4_tarski(D_64, E_65), B_67) | ~r2_hidden(E_65, A_66) | ~v1_relat_1(k8_relat_1(A_66, B_67)) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.82  tff(c_1282, plain, (![A_215, A_216, B_217]: (r1_tarski(A_215, k8_relat_1(A_216, B_217)) | ~v1_relat_1(A_215) | ~r2_hidden(k4_tarski('#skF_5'(A_215, k8_relat_1(A_216, B_217)), '#skF_6'(A_215, k8_relat_1(A_216, B_217))), B_217) | ~r2_hidden('#skF_6'(A_215, k8_relat_1(A_216, B_217)), A_216) | ~v1_relat_1(k8_relat_1(A_216, B_217)) | ~v1_relat_1(B_217))), inference(resolution, [status(thm)], [c_80, c_22])).
% 4.06/1.82  tff(c_1318, plain, (![A_75, A_216]: (~r2_hidden('#skF_6'(A_75, k8_relat_1(A_216, '#skF_9')), A_216) | ~v1_relat_1(k8_relat_1(A_216, '#skF_9')) | ~v1_relat_1('#skF_9') | ~r1_tarski(A_75, '#skF_8') | r1_tarski(A_75, k8_relat_1(A_216, '#skF_9')) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_124, c_1282])).
% 4.06/1.82  tff(c_1415, plain, (![A_222, A_223]: (~r2_hidden('#skF_6'(A_222, k8_relat_1(A_223, '#skF_9')), A_223) | ~v1_relat_1(k8_relat_1(A_223, '#skF_9')) | ~r1_tarski(A_222, '#skF_8') | r1_tarski(A_222, k8_relat_1(A_223, '#skF_9')) | ~v1_relat_1(A_222))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1318])).
% 4.06/1.82  tff(c_1423, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | ~r1_tarski(k8_relat_1('#skF_7', '#skF_8'), '#skF_8') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_8')) | r1_tarski(k8_relat_1('#skF_7', '#skF_8'), k8_relat_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_888, c_1415])).
% 4.06/1.82  tff(c_1435, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | r1_tarski(k8_relat_1('#skF_7', '#skF_8'), k8_relat_1('#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_1152, c_1423])).
% 4.06/1.82  tff(c_1436, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_28, c_1435])).
% 4.06/1.82  tff(c_1441, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_1436])).
% 4.06/1.82  tff(c_1445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1441])).
% 4.06/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.82  
% 4.06/1.82  Inference rules
% 4.06/1.82  ----------------------
% 4.06/1.82  #Ref     : 0
% 4.06/1.82  #Sup     : 305
% 4.06/1.82  #Fact    : 0
% 4.06/1.82  #Define  : 0
% 4.06/1.82  #Split   : 3
% 4.06/1.82  #Chain   : 0
% 4.06/1.82  #Close   : 0
% 4.06/1.82  
% 4.06/1.82  Ordering : KBO
% 4.06/1.82  
% 4.06/1.82  Simplification rules
% 4.06/1.82  ----------------------
% 4.06/1.82  #Subsume      : 85
% 4.06/1.82  #Demod        : 227
% 4.06/1.82  #Tautology    : 26
% 4.06/1.82  #SimpNegUnit  : 1
% 4.06/1.82  #BackRed      : 0
% 4.06/1.82  
% 4.06/1.82  #Partial instantiations: 0
% 4.06/1.82  #Strategies tried      : 1
% 4.06/1.82  
% 4.06/1.82  Timing (in seconds)
% 4.06/1.82  ----------------------
% 4.06/1.82  Preprocessing        : 0.28
% 4.06/1.82  Parsing              : 0.13
% 4.06/1.82  CNF conversion       : 0.02
% 4.06/1.82  Main loop            : 0.63
% 4.06/1.82  Inferencing          : 0.22
% 4.06/1.82  Reduction            : 0.16
% 4.06/1.82  Demodulation         : 0.10
% 4.06/1.82  BG Simplification    : 0.03
% 4.06/1.82  Subsumption          : 0.19
% 4.06/1.82  Abstraction          : 0.03
% 4.06/1.82  MUC search           : 0.00
% 4.06/1.82  Cooper               : 0.00
% 4.06/1.82  Total                : 0.95
% 4.06/1.82  Index Insertion      : 0.00
% 4.06/1.82  Index Deletion       : 0.00
% 4.06/1.82  Index Matching       : 0.00
% 4.06/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
