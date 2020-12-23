%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:18 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  104 (1167 expanded)
%              Number of leaves         :   23 ( 397 expanded)
%              Depth                    :   26
%              Number of atoms          :  290 (4343 expanded)
%              Number of equality atoms :   13 ( 258 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

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

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k8_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_19,B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),A_19)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [D_63,E_64,B_65,A_66] :
      ( r2_hidden(k4_tarski(D_63,E_64),B_65)
      | ~ r2_hidden(k4_tarski(D_63,E_64),k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_208,plain,(
    ! [A_96,B_97,B_98] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_96,B_97),B_98),'#skF_6'(k8_relat_1(A_96,B_97),B_98)),B_97)
      | ~ v1_relat_1(B_97)
      | r1_tarski(k8_relat_1(A_96,B_97),B_98)
      | ~ v1_relat_1(k8_relat_1(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_20,plain,(
    ! [C_34,D_35,B_29,A_19] :
      ( r2_hidden(k4_tarski(C_34,D_35),B_29)
      | ~ r2_hidden(k4_tarski(C_34,D_35),A_19)
      | ~ r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_397,plain,(
    ! [A_139,B_140,B_141,B_142] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_139,B_140),B_141),'#skF_6'(k8_relat_1(A_139,B_140),B_141)),B_142)
      | ~ r1_tarski(B_140,B_142)
      | ~ v1_relat_1(B_140)
      | r1_tarski(k8_relat_1(A_139,B_140),B_141)
      | ~ v1_relat_1(k8_relat_1(A_139,B_140)) ) ),
    inference(resolution,[status(thm)],[c_208,c_20])).

tff(c_22,plain,(
    ! [A_19,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),B_29)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_422,plain,(
    ! [B_143,B_144,A_145] :
      ( ~ r1_tarski(B_143,B_144)
      | ~ v1_relat_1(B_143)
      | r1_tarski(k8_relat_1(A_145,B_143),B_144)
      | ~ v1_relat_1(k8_relat_1(A_145,B_143)) ) ),
    inference(resolution,[status(thm)],[c_397,c_22])).

tff(c_30,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_439,plain,
    ( ~ r1_tarski('#skF_9',k8_relat_1('#skF_8','#skF_10'))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_422,c_30])).

tff(c_448,plain,
    ( ~ r1_tarski('#skF_9',k8_relat_1('#skF_8','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_439])).

tff(c_449,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_452,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_449])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_452])).

tff(c_458,plain,(
    v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_226,plain,(
    ! [B_97,A_96] :
      ( ~ v1_relat_1(B_97)
      | r1_tarski(k8_relat_1(A_96,B_97),B_97)
      | ~ v1_relat_1(k8_relat_1(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_208,c_22])).

tff(c_10,plain,(
    ! [A_1,B_2,C_12] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),B_2)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),C_12)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_459,plain,(
    ! [A_146,B_147,C_148] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_146,B_147,C_148),'#skF_2'(A_146,B_147,C_148)),C_148)
      | r2_hidden(k4_tarski('#skF_3'(A_146,B_147,C_148),'#skF_4'(A_146,B_147,C_148)),C_148)
      | k8_relat_1(A_146,B_147) = C_148
      | ~ v1_relat_1(C_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_470,plain,(
    ! [A_149,B_150] :
      ( r2_hidden(k4_tarski('#skF_3'(A_149,B_150,B_150),'#skF_4'(A_149,B_150,B_150)),B_150)
      | k8_relat_1(A_149,B_150) = B_150
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_10,c_459])).

tff(c_18,plain,(
    ! [E_18,A_1,D_17,B_2] :
      ( r2_hidden(E_18,A_1)
      | ~ r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_488,plain,(
    ! [A_149,A_1,B_2] :
      ( r2_hidden('#skF_4'(A_149,k8_relat_1(A_1,B_2),k8_relat_1(A_1,B_2)),A_1)
      | ~ v1_relat_1(B_2)
      | k8_relat_1(A_149,k8_relat_1(A_1,B_2)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(k8_relat_1(A_1,B_2)) ) ),
    inference(resolution,[status(thm)],[c_470,c_18])).

tff(c_468,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1,B_2,B_2),'#skF_4'(A_1,B_2,B_2)),B_2)
      | k8_relat_1(A_1,B_2) = B_2
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_10,c_459])).

tff(c_861,plain,(
    ! [A_222,B_223,C_224] :
      ( r2_hidden(k4_tarski('#skF_1'(A_222,B_223,C_224),'#skF_2'(A_222,B_223,C_224)),B_223)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_222,B_223,C_224),'#skF_4'(A_222,B_223,C_224)),B_223)
      | ~ r2_hidden('#skF_4'(A_222,B_223,C_224),A_222)
      | k8_relat_1(A_222,B_223) = C_224
      | ~ v1_relat_1(C_224)
      | ~ v1_relat_1(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2,C_12] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),C_12)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden('#skF_4'(A_1,B_2,C_12),A_1)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_893,plain,(
    ! [A_225,B_226] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_225,B_226,B_226),'#skF_4'(A_225,B_226,B_226)),B_226)
      | ~ r2_hidden('#skF_4'(A_225,B_226,B_226),A_225)
      | k8_relat_1(A_225,B_226) = B_226
      | ~ v1_relat_1(B_226) ) ),
    inference(resolution,[status(thm)],[c_861,c_2])).

tff(c_932,plain,(
    ! [A_227,B_228] :
      ( ~ r2_hidden('#skF_4'(A_227,B_228,B_228),A_227)
      | k8_relat_1(A_227,B_228) = B_228
      | ~ v1_relat_1(B_228) ) ),
    inference(resolution,[status(thm)],[c_468,c_893])).

tff(c_938,plain,(
    ! [B_229,A_230] :
      ( ~ v1_relat_1(B_229)
      | k8_relat_1(A_230,k8_relat_1(A_230,B_229)) = k8_relat_1(A_230,B_229)
      | ~ v1_relat_1(k8_relat_1(A_230,B_229)) ) ),
    inference(resolution,[status(thm)],[c_488,c_932])).

tff(c_940,plain,
    ( ~ v1_relat_1('#skF_9')
    | k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9')) = k8_relat_1('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_458,c_938])).

tff(c_945,plain,(
    k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9')) = k8_relat_1('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_940])).

tff(c_228,plain,(
    ! [B_103,A_104] :
      ( ~ v1_relat_1(B_103)
      | r1_tarski(k8_relat_1(A_104,B_103),B_103)
      | ~ v1_relat_1(k8_relat_1(A_104,B_103)) ) ),
    inference(resolution,[status(thm)],[c_208,c_22])).

tff(c_34,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    ! [C_51,D_52,B_53,A_54] :
      ( r2_hidden(k4_tarski(C_51,D_52),B_53)
      | ~ r2_hidden(k4_tarski(C_51,D_52),A_54)
      | ~ r1_tarski(A_54,B_53)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_60,B_61,B_62] :
      ( r2_hidden(k4_tarski('#skF_5'(A_60,B_61),'#skF_6'(A_60,B_61)),B_62)
      | ~ r1_tarski(A_60,B_62)
      | r1_tarski(A_60,B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_110,plain,(
    ! [A_78,B_79,B_80,B_81] :
      ( r2_hidden(k4_tarski('#skF_5'(A_78,B_79),'#skF_6'(A_78,B_79)),B_80)
      | ~ r1_tarski(B_81,B_80)
      | ~ v1_relat_1(B_81)
      | ~ r1_tarski(A_78,B_81)
      | r1_tarski(A_78,B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_59,c_20])).

tff(c_116,plain,(
    ! [A_78,B_79] :
      ( r2_hidden(k4_tarski('#skF_5'(A_78,B_79),'#skF_6'(A_78,B_79)),'#skF_10')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_78,'#skF_9')
      | r1_tarski(A_78,B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_125,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(k4_tarski('#skF_5'(A_82,B_83),'#skF_6'(A_82,B_83)),'#skF_10')
      | ~ r1_tarski(A_82,'#skF_9')
      | r1_tarski(A_82,B_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_116])).

tff(c_137,plain,(
    ! [A_84] :
      ( ~ r1_tarski(A_84,'#skF_9')
      | r1_tarski(A_84,'#skF_10')
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_125,c_22])).

tff(c_71,plain,(
    ! [A_60,B_61,B_29,B_62] :
      ( r2_hidden(k4_tarski('#skF_5'(A_60,B_61),'#skF_6'(A_60,B_61)),B_29)
      | ~ r1_tarski(B_62,B_29)
      | ~ v1_relat_1(B_62)
      | ~ r1_tarski(A_60,B_62)
      | r1_tarski(A_60,B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_59,c_20])).

tff(c_140,plain,(
    ! [A_60,B_61,A_84] :
      ( r2_hidden(k4_tarski('#skF_5'(A_60,B_61),'#skF_6'(A_60,B_61)),'#skF_10')
      | ~ r1_tarski(A_60,A_84)
      | r1_tarski(A_60,B_61)
      | ~ v1_relat_1(A_60)
      | ~ r1_tarski(A_84,'#skF_9')
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_137,c_71])).

tff(c_695,plain,(
    ! [A_195,B_196,B_197] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_195,B_196),B_197),'#skF_6'(k8_relat_1(A_195,B_196),B_197)),'#skF_10')
      | r1_tarski(k8_relat_1(A_195,B_196),B_197)
      | ~ r1_tarski(B_196,'#skF_9')
      | ~ v1_relat_1(B_196)
      | ~ v1_relat_1(k8_relat_1(A_195,B_196)) ) ),
    inference(resolution,[status(thm)],[c_228,c_140])).

tff(c_713,plain,(
    ! [A_195,B_196] :
      ( r1_tarski(k8_relat_1(A_195,B_196),'#skF_10')
      | ~ r1_tarski(B_196,'#skF_9')
      | ~ v1_relat_1(B_196)
      | ~ v1_relat_1(k8_relat_1(A_195,B_196)) ) ),
    inference(resolution,[status(thm)],[c_695,c_22])).

tff(c_968,plain,
    ( r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_10')
    | ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
    | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_713])).

tff(c_1054,plain,
    ( r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_10')
    | ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_945,c_458,c_968])).

tff(c_1385,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1054])).

tff(c_1424,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_226,c_1385])).

tff(c_1431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_38,c_1424])).

tff(c_1433,plain,(
    r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1054])).

tff(c_28,plain,(
    ! [A_38,C_40,B_39] :
      ( r1_tarski(k8_relat_1(A_38,C_40),k8_relat_1(B_39,C_40))
      | ~ r1_tarski(A_38,B_39)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [A_74,B_75,A_76,B_77] :
      ( r2_hidden('#skF_6'(A_74,B_75),A_76)
      | ~ v1_relat_1(k8_relat_1(A_76,B_77))
      | ~ v1_relat_1(B_77)
      | ~ r1_tarski(A_74,k8_relat_1(A_76,B_77))
      | r1_tarski(A_74,B_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_59,c_18])).

tff(c_109,plain,(
    ! [A_38,C_40,B_75,B_39] :
      ( r2_hidden('#skF_6'(k8_relat_1(A_38,C_40),B_75),B_39)
      | ~ v1_relat_1(k8_relat_1(B_39,C_40))
      | r1_tarski(k8_relat_1(A_38,C_40),B_75)
      | ~ v1_relat_1(k8_relat_1(A_38,C_40))
      | ~ r1_tarski(A_38,B_39)
      | ~ v1_relat_1(C_40) ) ),
    inference(resolution,[status(thm)],[c_28,c_102])).

tff(c_1011,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
    | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_7','#skF_9'))
    | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_945,c_226])).

tff(c_1086,plain,(
    r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_7','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_945,c_458,c_1011])).

tff(c_51,plain,(
    ! [A_19,B_29,B_53] :
      ( r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),B_53)
      | ~ r1_tarski(A_19,B_53)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_82,plain,(
    ! [A_19,B_29,B_65,A_66] :
      ( r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),B_65)
      | ~ v1_relat_1(k8_relat_1(A_66,B_65))
      | ~ v1_relat_1(B_65)
      | ~ r1_tarski(A_19,k8_relat_1(A_66,B_65))
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(resolution,[status(thm)],[c_51,c_73])).

tff(c_1123,plain,(
    ! [B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1('#skF_7','#skF_9'),B_29),'#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_29)),'#skF_9')
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),B_29)
      | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1086,c_82])).

tff(c_1152,plain,(
    ! [B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1('#skF_7','#skF_9'),B_29),'#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_29)),'#skF_9')
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),B_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_38,c_1123])).

tff(c_85,plain,(
    ! [D_70,E_71,A_72,B_73] :
      ( r2_hidden(k4_tarski(D_70,E_71),k8_relat_1(A_72,B_73))
      | ~ r2_hidden(k4_tarski(D_70,E_71),B_73)
      | ~ r2_hidden(E_71,A_72)
      | ~ v1_relat_1(k8_relat_1(A_72,B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2591,plain,(
    ! [A_301,A_302,B_303] :
      ( r1_tarski(A_301,k8_relat_1(A_302,B_303))
      | ~ v1_relat_1(A_301)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_301,k8_relat_1(A_302,B_303)),'#skF_6'(A_301,k8_relat_1(A_302,B_303))),B_303)
      | ~ r2_hidden('#skF_6'(A_301,k8_relat_1(A_302,B_303)),A_302)
      | ~ v1_relat_1(k8_relat_1(A_302,B_303))
      | ~ v1_relat_1(B_303) ) ),
    inference(resolution,[status(thm)],[c_85,c_22])).

tff(c_2595,plain,(
    ! [A_302] :
      ( ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
      | ~ r2_hidden('#skF_6'(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(A_302,'#skF_9')),A_302)
      | ~ v1_relat_1(k8_relat_1(A_302,'#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(A_302,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1152,c_2591])).

tff(c_4736,plain,(
    ! [A_384] :
      ( ~ r2_hidden('#skF_6'(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(A_384,'#skF_9')),A_384)
      | ~ v1_relat_1(k8_relat_1(A_384,'#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(A_384,'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_458,c_2595])).

tff(c_4748,plain,(
    ! [B_39] :
      ( ~ v1_relat_1(k8_relat_1(B_39,'#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(B_39,'#skF_9'))
      | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
      | ~ r1_tarski('#skF_7',B_39)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_109,c_4736])).

tff(c_4765,plain,(
    ! [B_385] :
      ( ~ v1_relat_1(k8_relat_1(B_385,'#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(B_385,'#skF_9'))
      | ~ r1_tarski('#skF_7',B_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_458,c_4748])).

tff(c_70,plain,(
    ! [A_60,B_61,A_1,B_2] :
      ( r2_hidden('#skF_6'(A_60,B_61),A_1)
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ r1_tarski(A_60,k8_relat_1(A_1,B_2))
      | r1_tarski(A_60,B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_59,c_18])).

tff(c_4807,plain,(
    ! [B_61,B_385] :
      ( r2_hidden('#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_61),B_385)
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),B_61)
      | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
      | ~ v1_relat_1(k8_relat_1(B_385,'#skF_9'))
      | ~ r1_tarski('#skF_7',B_385) ) ),
    inference(resolution,[status(thm)],[c_4765,c_70])).

tff(c_5029,plain,(
    ! [B_390,B_391] :
      ( r2_hidden('#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_390),B_391)
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),B_390)
      | ~ v1_relat_1(k8_relat_1(B_391,'#skF_9'))
      | ~ r1_tarski('#skF_7',B_391) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_38,c_4807])).

tff(c_123,plain,(
    ! [A_78,B_79] :
      ( r2_hidden(k4_tarski('#skF_5'(A_78,B_79),'#skF_6'(A_78,B_79)),'#skF_10')
      | ~ r1_tarski(A_78,'#skF_9')
      | r1_tarski(A_78,B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_116])).

tff(c_2641,plain,(
    ! [A_78,A_302] :
      ( ~ r2_hidden('#skF_6'(A_78,k8_relat_1(A_302,'#skF_10')),A_302)
      | ~ v1_relat_1(k8_relat_1(A_302,'#skF_10'))
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski(A_78,'#skF_9')
      | r1_tarski(A_78,k8_relat_1(A_302,'#skF_10'))
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_123,c_2591])).

tff(c_2675,plain,(
    ! [A_78,A_302] :
      ( ~ r2_hidden('#skF_6'(A_78,k8_relat_1(A_302,'#skF_10')),A_302)
      | ~ v1_relat_1(k8_relat_1(A_302,'#skF_10'))
      | ~ r1_tarski(A_78,'#skF_9')
      | r1_tarski(A_78,k8_relat_1(A_302,'#skF_10'))
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2641])).

tff(c_5041,plain,(
    ! [B_391] :
      ( ~ v1_relat_1(k8_relat_1(B_391,'#skF_10'))
      | ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),'#skF_9')
      | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(B_391,'#skF_10'))
      | ~ v1_relat_1(k8_relat_1(B_391,'#skF_9'))
      | ~ r1_tarski('#skF_7',B_391) ) ),
    inference(resolution,[status(thm)],[c_5029,c_2675])).

tff(c_5059,plain,(
    ! [B_392] :
      ( ~ v1_relat_1(k8_relat_1(B_392,'#skF_10'))
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(B_392,'#skF_10'))
      | ~ v1_relat_1(k8_relat_1(B_392,'#skF_9'))
      | ~ r1_tarski('#skF_7',B_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_1433,c_5041])).

tff(c_5086,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9'))
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_5059,c_30])).

tff(c_5125,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10'))
    | ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5086])).

tff(c_5126,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_5125])).

tff(c_5129,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_5126])).

tff(c_5133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5129])).

tff(c_5134,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_8','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_5125])).

tff(c_5138,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_5134])).

tff(c_5142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.58/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/2.61  
% 7.97/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/2.61  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 7.97/2.61  
% 7.97/2.61  %Foreground sorts:
% 7.97/2.61  
% 7.97/2.61  
% 7.97/2.61  %Background operators:
% 7.97/2.61  
% 7.97/2.61  
% 7.97/2.61  %Foreground operators:
% 7.97/2.61  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 7.97/2.61  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.97/2.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.97/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.97/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.97/2.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.97/2.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.97/2.61  tff('#skF_7', type, '#skF_7': $i).
% 7.97/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.97/2.61  tff('#skF_10', type, '#skF_10': $i).
% 7.97/2.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.97/2.61  tff('#skF_9', type, '#skF_9': $i).
% 7.97/2.61  tff('#skF_8', type, '#skF_8': $i).
% 7.97/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.97/2.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.97/2.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.97/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.97/2.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.97/2.61  
% 7.97/2.63  tff(f_71, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 7.97/2.63  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 7.97/2.63  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 7.97/2.63  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 7.97/2.63  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t131_relat_1)).
% 7.97/2.63  tff(c_36, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.97/2.63  tff(c_26, plain, (![A_36, B_37]: (v1_relat_1(k8_relat_1(A_36, B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.97/2.63  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.97/2.63  tff(c_32, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.97/2.63  tff(c_24, plain, (![A_19, B_29]: (r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), A_19) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.97/2.63  tff(c_73, plain, (![D_63, E_64, B_65, A_66]: (r2_hidden(k4_tarski(D_63, E_64), B_65) | ~r2_hidden(k4_tarski(D_63, E_64), k8_relat_1(A_66, B_65)) | ~v1_relat_1(k8_relat_1(A_66, B_65)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.97/2.63  tff(c_208, plain, (![A_96, B_97, B_98]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_96, B_97), B_98), '#skF_6'(k8_relat_1(A_96, B_97), B_98)), B_97) | ~v1_relat_1(B_97) | r1_tarski(k8_relat_1(A_96, B_97), B_98) | ~v1_relat_1(k8_relat_1(A_96, B_97)))), inference(resolution, [status(thm)], [c_24, c_73])).
% 7.97/2.64  tff(c_20, plain, (![C_34, D_35, B_29, A_19]: (r2_hidden(k4_tarski(C_34, D_35), B_29) | ~r2_hidden(k4_tarski(C_34, D_35), A_19) | ~r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.97/2.64  tff(c_397, plain, (![A_139, B_140, B_141, B_142]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_139, B_140), B_141), '#skF_6'(k8_relat_1(A_139, B_140), B_141)), B_142) | ~r1_tarski(B_140, B_142) | ~v1_relat_1(B_140) | r1_tarski(k8_relat_1(A_139, B_140), B_141) | ~v1_relat_1(k8_relat_1(A_139, B_140)))), inference(resolution, [status(thm)], [c_208, c_20])).
% 7.97/2.64  tff(c_22, plain, (![A_19, B_29]: (~r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), B_29) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.97/2.64  tff(c_422, plain, (![B_143, B_144, A_145]: (~r1_tarski(B_143, B_144) | ~v1_relat_1(B_143) | r1_tarski(k8_relat_1(A_145, B_143), B_144) | ~v1_relat_1(k8_relat_1(A_145, B_143)))), inference(resolution, [status(thm)], [c_397, c_22])).
% 7.97/2.64  tff(c_30, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1('#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.97/2.64  tff(c_439, plain, (~r1_tarski('#skF_9', k8_relat_1('#skF_8', '#skF_10')) | ~v1_relat_1('#skF_9') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_422, c_30])).
% 7.97/2.64  tff(c_448, plain, (~r1_tarski('#skF_9', k8_relat_1('#skF_8', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_439])).
% 7.97/2.64  tff(c_449, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(splitLeft, [status(thm)], [c_448])).
% 7.97/2.64  tff(c_452, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_449])).
% 7.97/2.64  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_452])).
% 7.97/2.64  tff(c_458, plain, (v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(splitRight, [status(thm)], [c_448])).
% 7.97/2.64  tff(c_226, plain, (![B_97, A_96]: (~v1_relat_1(B_97) | r1_tarski(k8_relat_1(A_96, B_97), B_97) | ~v1_relat_1(k8_relat_1(A_96, B_97)))), inference(resolution, [status(thm)], [c_208, c_22])).
% 7.97/2.64  tff(c_10, plain, (![A_1, B_2, C_12]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), B_2) | r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), C_12) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.97/2.64  tff(c_459, plain, (![A_146, B_147, C_148]: (~r2_hidden(k4_tarski('#skF_1'(A_146, B_147, C_148), '#skF_2'(A_146, B_147, C_148)), C_148) | r2_hidden(k4_tarski('#skF_3'(A_146, B_147, C_148), '#skF_4'(A_146, B_147, C_148)), C_148) | k8_relat_1(A_146, B_147)=C_148 | ~v1_relat_1(C_148) | ~v1_relat_1(B_147))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.97/2.64  tff(c_470, plain, (![A_149, B_150]: (r2_hidden(k4_tarski('#skF_3'(A_149, B_150, B_150), '#skF_4'(A_149, B_150, B_150)), B_150) | k8_relat_1(A_149, B_150)=B_150 | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_10, c_459])).
% 7.97/2.64  tff(c_18, plain, (![E_18, A_1, D_17, B_2]: (r2_hidden(E_18, A_1) | ~r2_hidden(k4_tarski(D_17, E_18), k8_relat_1(A_1, B_2)) | ~v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.97/2.64  tff(c_488, plain, (![A_149, A_1, B_2]: (r2_hidden('#skF_4'(A_149, k8_relat_1(A_1, B_2), k8_relat_1(A_1, B_2)), A_1) | ~v1_relat_1(B_2) | k8_relat_1(A_149, k8_relat_1(A_1, B_2))=k8_relat_1(A_1, B_2) | ~v1_relat_1(k8_relat_1(A_1, B_2)))), inference(resolution, [status(thm)], [c_470, c_18])).
% 7.97/2.64  tff(c_468, plain, (![A_1, B_2]: (r2_hidden(k4_tarski('#skF_3'(A_1, B_2, B_2), '#skF_4'(A_1, B_2, B_2)), B_2) | k8_relat_1(A_1, B_2)=B_2 | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_10, c_459])).
% 7.97/2.64  tff(c_861, plain, (![A_222, B_223, C_224]: (r2_hidden(k4_tarski('#skF_1'(A_222, B_223, C_224), '#skF_2'(A_222, B_223, C_224)), B_223) | ~r2_hidden(k4_tarski('#skF_3'(A_222, B_223, C_224), '#skF_4'(A_222, B_223, C_224)), B_223) | ~r2_hidden('#skF_4'(A_222, B_223, C_224), A_222) | k8_relat_1(A_222, B_223)=C_224 | ~v1_relat_1(C_224) | ~v1_relat_1(B_223))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.97/2.64  tff(c_2, plain, (![A_1, B_2, C_12]: (~r2_hidden(k4_tarski('#skF_1'(A_1, B_2, C_12), '#skF_2'(A_1, B_2, C_12)), C_12) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_2, C_12), '#skF_4'(A_1, B_2, C_12)), B_2) | ~r2_hidden('#skF_4'(A_1, B_2, C_12), A_1) | k8_relat_1(A_1, B_2)=C_12 | ~v1_relat_1(C_12) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.97/2.64  tff(c_893, plain, (![A_225, B_226]: (~r2_hidden(k4_tarski('#skF_3'(A_225, B_226, B_226), '#skF_4'(A_225, B_226, B_226)), B_226) | ~r2_hidden('#skF_4'(A_225, B_226, B_226), A_225) | k8_relat_1(A_225, B_226)=B_226 | ~v1_relat_1(B_226))), inference(resolution, [status(thm)], [c_861, c_2])).
% 7.97/2.64  tff(c_932, plain, (![A_227, B_228]: (~r2_hidden('#skF_4'(A_227, B_228, B_228), A_227) | k8_relat_1(A_227, B_228)=B_228 | ~v1_relat_1(B_228))), inference(resolution, [status(thm)], [c_468, c_893])).
% 7.97/2.64  tff(c_938, plain, (![B_229, A_230]: (~v1_relat_1(B_229) | k8_relat_1(A_230, k8_relat_1(A_230, B_229))=k8_relat_1(A_230, B_229) | ~v1_relat_1(k8_relat_1(A_230, B_229)))), inference(resolution, [status(thm)], [c_488, c_932])).
% 7.97/2.64  tff(c_940, plain, (~v1_relat_1('#skF_9') | k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_9'))=k8_relat_1('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_458, c_938])).
% 7.97/2.64  tff(c_945, plain, (k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_9'))=k8_relat_1('#skF_7', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_940])).
% 7.97/2.64  tff(c_228, plain, (![B_103, A_104]: (~v1_relat_1(B_103) | r1_tarski(k8_relat_1(A_104, B_103), B_103) | ~v1_relat_1(k8_relat_1(A_104, B_103)))), inference(resolution, [status(thm)], [c_208, c_22])).
% 7.97/2.64  tff(c_34, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.97/2.64  tff(c_48, plain, (![C_51, D_52, B_53, A_54]: (r2_hidden(k4_tarski(C_51, D_52), B_53) | ~r2_hidden(k4_tarski(C_51, D_52), A_54) | ~r1_tarski(A_54, B_53) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.97/2.64  tff(c_59, plain, (![A_60, B_61, B_62]: (r2_hidden(k4_tarski('#skF_5'(A_60, B_61), '#skF_6'(A_60, B_61)), B_62) | ~r1_tarski(A_60, B_62) | r1_tarski(A_60, B_61) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_24, c_48])).
% 7.97/2.64  tff(c_110, plain, (![A_78, B_79, B_80, B_81]: (r2_hidden(k4_tarski('#skF_5'(A_78, B_79), '#skF_6'(A_78, B_79)), B_80) | ~r1_tarski(B_81, B_80) | ~v1_relat_1(B_81) | ~r1_tarski(A_78, B_81) | r1_tarski(A_78, B_79) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_59, c_20])).
% 7.97/2.64  tff(c_116, plain, (![A_78, B_79]: (r2_hidden(k4_tarski('#skF_5'(A_78, B_79), '#skF_6'(A_78, B_79)), '#skF_10') | ~v1_relat_1('#skF_9') | ~r1_tarski(A_78, '#skF_9') | r1_tarski(A_78, B_79) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_34, c_110])).
% 7.97/2.64  tff(c_125, plain, (![A_82, B_83]: (r2_hidden(k4_tarski('#skF_5'(A_82, B_83), '#skF_6'(A_82, B_83)), '#skF_10') | ~r1_tarski(A_82, '#skF_9') | r1_tarski(A_82, B_83) | ~v1_relat_1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_116])).
% 7.97/2.64  tff(c_137, plain, (![A_84]: (~r1_tarski(A_84, '#skF_9') | r1_tarski(A_84, '#skF_10') | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_125, c_22])).
% 7.97/2.64  tff(c_71, plain, (![A_60, B_61, B_29, B_62]: (r2_hidden(k4_tarski('#skF_5'(A_60, B_61), '#skF_6'(A_60, B_61)), B_29) | ~r1_tarski(B_62, B_29) | ~v1_relat_1(B_62) | ~r1_tarski(A_60, B_62) | r1_tarski(A_60, B_61) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_59, c_20])).
% 7.97/2.64  tff(c_140, plain, (![A_60, B_61, A_84]: (r2_hidden(k4_tarski('#skF_5'(A_60, B_61), '#skF_6'(A_60, B_61)), '#skF_10') | ~r1_tarski(A_60, A_84) | r1_tarski(A_60, B_61) | ~v1_relat_1(A_60) | ~r1_tarski(A_84, '#skF_9') | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_137, c_71])).
% 7.97/2.64  tff(c_695, plain, (![A_195, B_196, B_197]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_195, B_196), B_197), '#skF_6'(k8_relat_1(A_195, B_196), B_197)), '#skF_10') | r1_tarski(k8_relat_1(A_195, B_196), B_197) | ~r1_tarski(B_196, '#skF_9') | ~v1_relat_1(B_196) | ~v1_relat_1(k8_relat_1(A_195, B_196)))), inference(resolution, [status(thm)], [c_228, c_140])).
% 7.97/2.64  tff(c_713, plain, (![A_195, B_196]: (r1_tarski(k8_relat_1(A_195, B_196), '#skF_10') | ~r1_tarski(B_196, '#skF_9') | ~v1_relat_1(B_196) | ~v1_relat_1(k8_relat_1(A_195, B_196)))), inference(resolution, [status(thm)], [c_695, c_22])).
% 7.97/2.64  tff(c_968, plain, (r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_10') | ~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_9') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | ~v1_relat_1(k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_945, c_713])).
% 7.97/2.64  tff(c_1054, plain, (r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_10') | ~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_945, c_458, c_968])).
% 7.97/2.64  tff(c_1385, plain, (~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_9')), inference(splitLeft, [status(thm)], [c_1054])).
% 7.97/2.64  tff(c_1424, plain, (~v1_relat_1('#skF_9') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_226, c_1385])).
% 7.97/2.64  tff(c_1431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_38, c_1424])).
% 7.97/2.64  tff(c_1433, plain, (r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_1054])).
% 7.97/2.64  tff(c_28, plain, (![A_38, C_40, B_39]: (r1_tarski(k8_relat_1(A_38, C_40), k8_relat_1(B_39, C_40)) | ~r1_tarski(A_38, B_39) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.97/2.64  tff(c_102, plain, (![A_74, B_75, A_76, B_77]: (r2_hidden('#skF_6'(A_74, B_75), A_76) | ~v1_relat_1(k8_relat_1(A_76, B_77)) | ~v1_relat_1(B_77) | ~r1_tarski(A_74, k8_relat_1(A_76, B_77)) | r1_tarski(A_74, B_75) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_59, c_18])).
% 7.97/2.64  tff(c_109, plain, (![A_38, C_40, B_75, B_39]: (r2_hidden('#skF_6'(k8_relat_1(A_38, C_40), B_75), B_39) | ~v1_relat_1(k8_relat_1(B_39, C_40)) | r1_tarski(k8_relat_1(A_38, C_40), B_75) | ~v1_relat_1(k8_relat_1(A_38, C_40)) | ~r1_tarski(A_38, B_39) | ~v1_relat_1(C_40))), inference(resolution, [status(thm)], [c_28, c_102])).
% 7.97/2.64  tff(c_1011, plain, (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1('#skF_7', '#skF_9')) | ~v1_relat_1(k8_relat_1('#skF_7', k8_relat_1('#skF_7', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_945, c_226])).
% 7.97/2.64  tff(c_1086, plain, (r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1('#skF_7', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_945, c_458, c_1011])).
% 7.97/2.64  tff(c_51, plain, (![A_19, B_29, B_53]: (r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), B_53) | ~r1_tarski(A_19, B_53) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_24, c_48])).
% 7.97/2.64  tff(c_82, plain, (![A_19, B_29, B_65, A_66]: (r2_hidden(k4_tarski('#skF_5'(A_19, B_29), '#skF_6'(A_19, B_29)), B_65) | ~v1_relat_1(k8_relat_1(A_66, B_65)) | ~v1_relat_1(B_65) | ~r1_tarski(A_19, k8_relat_1(A_66, B_65)) | r1_tarski(A_19, B_29) | ~v1_relat_1(A_19))), inference(resolution, [status(thm)], [c_51, c_73])).
% 7.97/2.64  tff(c_1123, plain, (![B_29]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1('#skF_7', '#skF_9'), B_29), '#skF_6'(k8_relat_1('#skF_7', '#skF_9'), B_29)), '#skF_9') | ~v1_relat_1('#skF_9') | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), B_29) | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')))), inference(resolution, [status(thm)], [c_1086, c_82])).
% 7.97/2.64  tff(c_1152, plain, (![B_29]: (r2_hidden(k4_tarski('#skF_5'(k8_relat_1('#skF_7', '#skF_9'), B_29), '#skF_6'(k8_relat_1('#skF_7', '#skF_9'), B_29)), '#skF_9') | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), B_29))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_38, c_1123])).
% 7.97/2.64  tff(c_85, plain, (![D_70, E_71, A_72, B_73]: (r2_hidden(k4_tarski(D_70, E_71), k8_relat_1(A_72, B_73)) | ~r2_hidden(k4_tarski(D_70, E_71), B_73) | ~r2_hidden(E_71, A_72) | ~v1_relat_1(k8_relat_1(A_72, B_73)) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.97/2.64  tff(c_2591, plain, (![A_301, A_302, B_303]: (r1_tarski(A_301, k8_relat_1(A_302, B_303)) | ~v1_relat_1(A_301) | ~r2_hidden(k4_tarski('#skF_5'(A_301, k8_relat_1(A_302, B_303)), '#skF_6'(A_301, k8_relat_1(A_302, B_303))), B_303) | ~r2_hidden('#skF_6'(A_301, k8_relat_1(A_302, B_303)), A_302) | ~v1_relat_1(k8_relat_1(A_302, B_303)) | ~v1_relat_1(B_303))), inference(resolution, [status(thm)], [c_85, c_22])).
% 7.97/2.64  tff(c_2595, plain, (![A_302]: (~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | ~r2_hidden('#skF_6'(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1(A_302, '#skF_9')), A_302) | ~v1_relat_1(k8_relat_1(A_302, '#skF_9')) | ~v1_relat_1('#skF_9') | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1(A_302, '#skF_9')))), inference(resolution, [status(thm)], [c_1152, c_2591])).
% 7.97/2.64  tff(c_4736, plain, (![A_384]: (~r2_hidden('#skF_6'(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1(A_384, '#skF_9')), A_384) | ~v1_relat_1(k8_relat_1(A_384, '#skF_9')) | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1(A_384, '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_458, c_2595])).
% 7.97/2.64  tff(c_4748, plain, (![B_39]: (~v1_relat_1(k8_relat_1(B_39, '#skF_9')) | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1(B_39, '#skF_9')) | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | ~r1_tarski('#skF_7', B_39) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_109, c_4736])).
% 7.97/2.64  tff(c_4765, plain, (![B_385]: (~v1_relat_1(k8_relat_1(B_385, '#skF_9')) | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1(B_385, '#skF_9')) | ~r1_tarski('#skF_7', B_385))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_458, c_4748])).
% 7.97/2.64  tff(c_70, plain, (![A_60, B_61, A_1, B_2]: (r2_hidden('#skF_6'(A_60, B_61), A_1) | ~v1_relat_1(k8_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~r1_tarski(A_60, k8_relat_1(A_1, B_2)) | r1_tarski(A_60, B_61) | ~v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_59, c_18])).
% 7.97/2.64  tff(c_4807, plain, (![B_61, B_385]: (r2_hidden('#skF_6'(k8_relat_1('#skF_7', '#skF_9'), B_61), B_385) | ~v1_relat_1('#skF_9') | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), B_61) | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | ~v1_relat_1(k8_relat_1(B_385, '#skF_9')) | ~r1_tarski('#skF_7', B_385))), inference(resolution, [status(thm)], [c_4765, c_70])).
% 7.97/2.64  tff(c_5029, plain, (![B_390, B_391]: (r2_hidden('#skF_6'(k8_relat_1('#skF_7', '#skF_9'), B_390), B_391) | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), B_390) | ~v1_relat_1(k8_relat_1(B_391, '#skF_9')) | ~r1_tarski('#skF_7', B_391))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_38, c_4807])).
% 7.97/2.64  tff(c_123, plain, (![A_78, B_79]: (r2_hidden(k4_tarski('#skF_5'(A_78, B_79), '#skF_6'(A_78, B_79)), '#skF_10') | ~r1_tarski(A_78, '#skF_9') | r1_tarski(A_78, B_79) | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_116])).
% 7.97/2.64  tff(c_2641, plain, (![A_78, A_302]: (~r2_hidden('#skF_6'(A_78, k8_relat_1(A_302, '#skF_10')), A_302) | ~v1_relat_1(k8_relat_1(A_302, '#skF_10')) | ~v1_relat_1('#skF_10') | ~r1_tarski(A_78, '#skF_9') | r1_tarski(A_78, k8_relat_1(A_302, '#skF_10')) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_123, c_2591])).
% 7.97/2.64  tff(c_2675, plain, (![A_78, A_302]: (~r2_hidden('#skF_6'(A_78, k8_relat_1(A_302, '#skF_10')), A_302) | ~v1_relat_1(k8_relat_1(A_302, '#skF_10')) | ~r1_tarski(A_78, '#skF_9') | r1_tarski(A_78, k8_relat_1(A_302, '#skF_10')) | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2641])).
% 7.97/2.64  tff(c_5041, plain, (![B_391]: (~v1_relat_1(k8_relat_1(B_391, '#skF_10')) | ~r1_tarski(k8_relat_1('#skF_7', '#skF_9'), '#skF_9') | ~v1_relat_1(k8_relat_1('#skF_7', '#skF_9')) | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1(B_391, '#skF_10')) | ~v1_relat_1(k8_relat_1(B_391, '#skF_9')) | ~r1_tarski('#skF_7', B_391))), inference(resolution, [status(thm)], [c_5029, c_2675])).
% 7.97/2.64  tff(c_5059, plain, (![B_392]: (~v1_relat_1(k8_relat_1(B_392, '#skF_10')) | r1_tarski(k8_relat_1('#skF_7', '#skF_9'), k8_relat_1(B_392, '#skF_10')) | ~v1_relat_1(k8_relat_1(B_392, '#skF_9')) | ~r1_tarski('#skF_7', B_392))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_1433, c_5041])).
% 7.97/2.64  tff(c_5086, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_8', '#skF_9')) | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_5059, c_30])).
% 7.97/2.64  tff(c_5125, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_10')) | ~v1_relat_1(k8_relat_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5086])).
% 7.97/2.64  tff(c_5126, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_5125])).
% 7.97/2.64  tff(c_5129, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_5126])).
% 7.97/2.64  tff(c_5133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_5129])).
% 7.97/2.64  tff(c_5134, plain, (~v1_relat_1(k8_relat_1('#skF_8', '#skF_10'))), inference(splitRight, [status(thm)], [c_5125])).
% 7.97/2.64  tff(c_5138, plain, (~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_26, c_5134])).
% 7.97/2.64  tff(c_5142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_5138])).
% 7.97/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/2.64  
% 7.97/2.64  Inference rules
% 7.97/2.64  ----------------------
% 7.97/2.64  #Ref     : 0
% 7.97/2.64  #Sup     : 1137
% 7.97/2.64  #Fact    : 0
% 7.97/2.64  #Define  : 0
% 7.97/2.64  #Split   : 7
% 7.97/2.64  #Chain   : 0
% 7.97/2.64  #Close   : 0
% 7.97/2.64  
% 7.97/2.64  Ordering : KBO
% 7.97/2.64  
% 7.97/2.64  Simplification rules
% 7.97/2.64  ----------------------
% 7.97/2.64  #Subsume      : 294
% 7.97/2.64  #Demod        : 983
% 7.97/2.64  #Tautology    : 130
% 7.97/2.64  #SimpNegUnit  : 0
% 7.97/2.64  #BackRed      : 0
% 7.97/2.64  
% 7.97/2.64  #Partial instantiations: 0
% 7.97/2.64  #Strategies tried      : 1
% 7.97/2.64  
% 7.97/2.64  Timing (in seconds)
% 7.97/2.64  ----------------------
% 7.97/2.64  Preprocessing        : 0.30
% 7.97/2.64  Parsing              : 0.15
% 7.97/2.64  CNF conversion       : 0.03
% 7.97/2.64  Main loop            : 1.57
% 7.97/2.64  Inferencing          : 0.43
% 7.97/2.64  Reduction            : 0.41
% 7.97/2.64  Demodulation         : 0.29
% 7.97/2.64  BG Simplification    : 0.06
% 7.97/2.64  Subsumption          : 0.59
% 7.97/2.64  Abstraction          : 0.07
% 7.97/2.64  MUC search           : 0.00
% 7.97/2.64  Cooper               : 0.00
% 7.97/2.64  Total                : 1.91
% 7.97/2.64  Index Insertion      : 0.00
% 7.97/2.64  Index Deletion       : 0.00
% 7.97/2.64  Index Matching       : 0.00
% 7.97/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
