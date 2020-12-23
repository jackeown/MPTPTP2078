%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:55 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :  105 (1167 expanded)
%              Number of leaves         :   23 ( 397 expanded)
%              Depth                    :   26
%              Number of atoms          :  296 (4343 expanded)
%              Number of equality atoms :   13 ( 258 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

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
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k7_relat_1(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_20,B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_20)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [D_64,E_65,A_66,B_67] :
      ( r2_hidden(k4_tarski(D_64,E_65),A_66)
      | ~ r2_hidden(k4_tarski(D_64,E_65),k7_relat_1(A_66,B_67))
      | ~ v1_relat_1(k7_relat_1(A_66,B_67))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_208,plain,(
    ! [A_97,B_98,B_99] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_97,B_98),B_99),'#skF_6'(k7_relat_1(A_97,B_98),B_99)),A_97)
      | ~ v1_relat_1(A_97)
      | r1_tarski(k7_relat_1(A_97,B_98),B_99)
      | ~ v1_relat_1(k7_relat_1(A_97,B_98)) ) ),
    inference(resolution,[status(thm)],[c_24,c_73])).

tff(c_20,plain,(
    ! [C_35,D_36,B_30,A_20] :
      ( r2_hidden(k4_tarski(C_35,D_36),B_30)
      | ~ r2_hidden(k4_tarski(C_35,D_36),A_20)
      | ~ r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_397,plain,(
    ! [A_140,B_141,B_142,B_143] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_140,B_141),B_142),'#skF_6'(k7_relat_1(A_140,B_141),B_142)),B_143)
      | ~ r1_tarski(A_140,B_143)
      | ~ v1_relat_1(A_140)
      | r1_tarski(k7_relat_1(A_140,B_141),B_142)
      | ~ v1_relat_1(k7_relat_1(A_140,B_141)) ) ),
    inference(resolution,[status(thm)],[c_208,c_20])).

tff(c_22,plain,(
    ! [A_20,B_30] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_30)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_422,plain,(
    ! [A_144,B_145,B_146] :
      ( ~ r1_tarski(A_144,B_145)
      | ~ v1_relat_1(A_144)
      | r1_tarski(k7_relat_1(A_144,B_146),B_145)
      | ~ v1_relat_1(k7_relat_1(A_144,B_146)) ) ),
    inference(resolution,[status(thm)],[c_397,c_22])).

tff(c_30,plain,(
    ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_10','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_439,plain,
    ( ~ r1_tarski('#skF_9',k7_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_422,c_30])).

tff(c_448,plain,
    ( ~ r1_tarski('#skF_9',k7_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_439])).

tff(c_449,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_452,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_449])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_452])).

tff(c_458,plain,(
    v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_226,plain,(
    ! [A_97,B_98] :
      ( ~ v1_relat_1(A_97)
      | r1_tarski(k7_relat_1(A_97,B_98),A_97)
      | ~ v1_relat_1(k7_relat_1(A_97,B_98)) ) ),
    inference(resolution,[status(thm)],[c_208,c_22])).

tff(c_10,plain,(
    ! [A_1,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_12,C_13),'#skF_2'(A_1,B_12,C_13)),A_1)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_12,C_13),'#skF_4'(A_1,B_12,C_13)),C_13)
      | k7_relat_1(A_1,B_12) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_459,plain,(
    ! [A_147,B_148,C_149] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_147,B_148,C_149),'#skF_2'(A_147,B_148,C_149)),C_149)
      | r2_hidden(k4_tarski('#skF_3'(A_147,B_148,C_149),'#skF_4'(A_147,B_148,C_149)),C_149)
      | k7_relat_1(A_147,B_148) = C_149
      | ~ v1_relat_1(C_149)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_470,plain,(
    ! [A_150,B_151] :
      ( r2_hidden(k4_tarski('#skF_3'(A_150,B_151,A_150),'#skF_4'(A_150,B_151,A_150)),A_150)
      | k7_relat_1(A_150,B_151) = A_150
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_10,c_459])).

tff(c_18,plain,(
    ! [D_18,B_12,E_19,A_1] :
      ( r2_hidden(D_18,B_12)
      | ~ r2_hidden(k4_tarski(D_18,E_19),k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_488,plain,(
    ! [A_1,B_12,B_151] :
      ( r2_hidden('#skF_3'(k7_relat_1(A_1,B_12),B_151,k7_relat_1(A_1,B_12)),B_12)
      | ~ v1_relat_1(A_1)
      | k7_relat_1(k7_relat_1(A_1,B_12),B_151) = k7_relat_1(A_1,B_12)
      | ~ v1_relat_1(k7_relat_1(A_1,B_12)) ) ),
    inference(resolution,[status(thm)],[c_470,c_18])).

tff(c_468,plain,(
    ! [A_1,B_12] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1,B_12,A_1),'#skF_4'(A_1,B_12,A_1)),A_1)
      | k7_relat_1(A_1,B_12) = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_459])).

tff(c_4,plain,(
    ! [A_1,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_12,C_13),'#skF_2'(A_1,B_12,C_13)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_12,C_13),'#skF_4'(A_1,B_12,C_13)),A_1)
      | ~ r2_hidden('#skF_3'(A_1,B_12,C_13),B_12)
      | k7_relat_1(A_1,B_12) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_888,plain,(
    ! [A_226,B_227,C_228] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_226,B_227,C_228),'#skF_2'(A_226,B_227,C_228)),C_228)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_226,B_227,C_228),'#skF_4'(A_226,B_227,C_228)),A_226)
      | ~ r2_hidden('#skF_3'(A_226,B_227,C_228),B_227)
      | k7_relat_1(A_226,B_227) = C_228
      | ~ v1_relat_1(C_228)
      | ~ v1_relat_1(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_901,plain,(
    ! [A_229,B_230] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_229,B_230,A_229),'#skF_4'(A_229,B_230,A_229)),A_229)
      | ~ r2_hidden('#skF_3'(A_229,B_230,A_229),B_230)
      | k7_relat_1(A_229,B_230) = A_229
      | ~ v1_relat_1(A_229) ) ),
    inference(resolution,[status(thm)],[c_4,c_888])).

tff(c_940,plain,(
    ! [A_231,B_232] :
      ( ~ r2_hidden('#skF_3'(A_231,B_232,A_231),B_232)
      | k7_relat_1(A_231,B_232) = A_231
      | ~ v1_relat_1(A_231) ) ),
    inference(resolution,[status(thm)],[c_468,c_901])).

tff(c_946,plain,(
    ! [A_233,B_234] :
      ( ~ v1_relat_1(A_233)
      | k7_relat_1(k7_relat_1(A_233,B_234),B_234) = k7_relat_1(A_233,B_234)
      | ~ v1_relat_1(k7_relat_1(A_233,B_234)) ) ),
    inference(resolution,[status(thm)],[c_488,c_940])).

tff(c_948,plain,
    ( ~ v1_relat_1('#skF_9')
    | k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7') = k7_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_458,c_946])).

tff(c_953,plain,(
    k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7') = k7_relat_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_948])).

tff(c_228,plain,(
    ! [A_104,B_105] :
      ( ~ v1_relat_1(A_104)
      | r1_tarski(k7_relat_1(A_104,B_105),A_104)
      | ~ v1_relat_1(k7_relat_1(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_208,c_22])).

tff(c_34,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    ! [C_52,D_53,B_54,A_55] :
      ( r2_hidden(k4_tarski(C_52,D_53),B_54)
      | ~ r2_hidden(k4_tarski(C_52,D_53),A_55)
      | ~ r1_tarski(A_55,B_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_61,B_62,B_63] :
      ( r2_hidden(k4_tarski('#skF_5'(A_61,B_62),'#skF_6'(A_61,B_62)),B_63)
      | ~ r1_tarski(A_61,B_63)
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_110,plain,(
    ! [A_79,B_80,B_81,B_82] :
      ( r2_hidden(k4_tarski('#skF_5'(A_79,B_80),'#skF_6'(A_79,B_80)),B_81)
      | ~ r1_tarski(B_82,B_81)
      | ~ v1_relat_1(B_82)
      | ~ r1_tarski(A_79,B_82)
      | r1_tarski(A_79,B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_59,c_20])).

tff(c_116,plain,(
    ! [A_79,B_80] :
      ( r2_hidden(k4_tarski('#skF_5'(A_79,B_80),'#skF_6'(A_79,B_80)),'#skF_10')
      | ~ v1_relat_1('#skF_9')
      | ~ r1_tarski(A_79,'#skF_9')
      | r1_tarski(A_79,B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_34,c_110])).

tff(c_125,plain,(
    ! [A_83,B_84] :
      ( r2_hidden(k4_tarski('#skF_5'(A_83,B_84),'#skF_6'(A_83,B_84)),'#skF_10')
      | ~ r1_tarski(A_83,'#skF_9')
      | r1_tarski(A_83,B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_116])).

tff(c_137,plain,(
    ! [A_85] :
      ( ~ r1_tarski(A_85,'#skF_9')
      | r1_tarski(A_85,'#skF_10')
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_125,c_22])).

tff(c_71,plain,(
    ! [A_61,B_62,B_30,B_63] :
      ( r2_hidden(k4_tarski('#skF_5'(A_61,B_62),'#skF_6'(A_61,B_62)),B_30)
      | ~ r1_tarski(B_63,B_30)
      | ~ v1_relat_1(B_63)
      | ~ r1_tarski(A_61,B_63)
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_59,c_20])).

tff(c_140,plain,(
    ! [A_61,B_62,A_85] :
      ( r2_hidden(k4_tarski('#skF_5'(A_61,B_62),'#skF_6'(A_61,B_62)),'#skF_10')
      | ~ r1_tarski(A_61,A_85)
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61)
      | ~ r1_tarski(A_85,'#skF_9')
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_137,c_71])).

tff(c_689,plain,(
    ! [A_194,B_195,B_196] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_194,B_195),B_196),'#skF_6'(k7_relat_1(A_194,B_195),B_196)),'#skF_10')
      | r1_tarski(k7_relat_1(A_194,B_195),B_196)
      | ~ r1_tarski(A_194,'#skF_9')
      | ~ v1_relat_1(A_194)
      | ~ v1_relat_1(k7_relat_1(A_194,B_195)) ) ),
    inference(resolution,[status(thm)],[c_228,c_140])).

tff(c_707,plain,(
    ! [A_194,B_195] :
      ( r1_tarski(k7_relat_1(A_194,B_195),'#skF_10')
      | ~ r1_tarski(A_194,'#skF_9')
      | ~ v1_relat_1(A_194)
      | ~ v1_relat_1(k7_relat_1(A_194,B_195)) ) ),
    inference(resolution,[status(thm)],[c_689,c_22])).

tff(c_978,plain,
    ( r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_10')
    | ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_707])).

tff(c_1066,plain,
    ( r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_10')
    | ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_953,c_458,c_978])).

tff(c_1404,plain,(
    ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1066])).

tff(c_1431,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_226,c_1404])).

tff(c_1438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_38,c_1431])).

tff(c_1440,plain,(
    r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_1066])).

tff(c_28,plain,(
    ! [C_41,A_39,B_40] :
      ( r1_tarski(k7_relat_1(C_41,A_39),k7_relat_1(C_41,B_40))
      | ~ r1_tarski(A_39,B_40)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [A_75,B_76,B_77,A_78] :
      ( r2_hidden('#skF_5'(A_75,B_76),B_77)
      | ~ v1_relat_1(k7_relat_1(A_78,B_77))
      | ~ v1_relat_1(A_78)
      | ~ r1_tarski(A_75,k7_relat_1(A_78,B_77))
      | r1_tarski(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_59,c_18])).

tff(c_109,plain,(
    ! [C_41,A_39,B_76,B_40] :
      ( r2_hidden('#skF_5'(k7_relat_1(C_41,A_39),B_76),B_40)
      | ~ v1_relat_1(k7_relat_1(C_41,B_40))
      | r1_tarski(k7_relat_1(C_41,A_39),B_76)
      | ~ v1_relat_1(k7_relat_1(C_41,A_39))
      | ~ r1_tarski(A_39,B_40)
      | ~ v1_relat_1(C_41) ) ),
    inference(resolution,[status(thm)],[c_28,c_102])).

tff(c_1021,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
    | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_953,c_226])).

tff(c_1098,plain,(
    r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_953,c_458,c_1021])).

tff(c_51,plain,(
    ! [A_20,B_30,B_54] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_54)
      | ~ r1_tarski(A_20,B_54)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_82,plain,(
    ! [A_20,B_30,A_66,B_67] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_66)
      | ~ v1_relat_1(k7_relat_1(A_66,B_67))
      | ~ v1_relat_1(A_66)
      | ~ r1_tarski(A_20,k7_relat_1(A_66,B_67))
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_51,c_73])).

tff(c_1137,plain,(
    ! [B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_30),'#skF_6'(k7_relat_1('#skF_9','#skF_7'),B_30)),'#skF_9')
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_30)
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1098,c_82])).

tff(c_2818,plain,(
    ! [B_311] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_311),'#skF_6'(k7_relat_1('#skF_9','#skF_7'),B_311)),'#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_38,c_1137])).

tff(c_85,plain,(
    ! [D_71,E_72,A_73,B_74] :
      ( r2_hidden(k4_tarski(D_71,E_72),k7_relat_1(A_73,B_74))
      | ~ r2_hidden(k4_tarski(D_71,E_72),A_73)
      | ~ r2_hidden(D_71,B_74)
      | ~ v1_relat_1(k7_relat_1(A_73,B_74))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [A_20,A_73,B_74] :
      ( r1_tarski(A_20,k7_relat_1(A_73,B_74))
      | ~ v1_relat_1(A_20)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_20,k7_relat_1(A_73,B_74)),'#skF_6'(A_20,k7_relat_1(A_73,B_74))),A_73)
      | ~ r2_hidden('#skF_5'(A_20,k7_relat_1(A_73,B_74)),B_74)
      | ~ v1_relat_1(k7_relat_1(A_73,B_74))
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_85,c_22])).

tff(c_2824,plain,(
    ! [B_74] :
      ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | ~ r2_hidden('#skF_5'(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_74)),B_74)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_74))
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_74)) ) ),
    inference(resolution,[status(thm)],[c_2818,c_101])).

tff(c_4753,plain,(
    ! [B_388] :
      ( ~ r2_hidden('#skF_5'(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_388)),B_388)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_388))
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_388)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_458,c_2824])).

tff(c_4765,plain,(
    ! [B_40] :
      ( ~ v1_relat_1(k7_relat_1('#skF_9',B_40))
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_40))
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | ~ r1_tarski('#skF_7',B_40)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_109,c_4753])).

tff(c_4782,plain,(
    ! [B_389] :
      ( ~ v1_relat_1(k7_relat_1('#skF_9',B_389))
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_389))
      | ~ r1_tarski('#skF_7',B_389) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_458,c_4765])).

tff(c_70,plain,(
    ! [A_61,B_62,B_12,A_1] :
      ( r2_hidden('#skF_5'(A_61,B_62),B_12)
      | ~ v1_relat_1(k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(A_1)
      | ~ r1_tarski(A_61,k7_relat_1(A_1,B_12))
      | r1_tarski(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_59,c_18])).

tff(c_4826,plain,(
    ! [B_62,B_389] :
      ( r2_hidden('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_62),B_389)
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_62)
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_389))
      | ~ r1_tarski('#skF_7',B_389) ) ),
    inference(resolution,[status(thm)],[c_4782,c_70])).

tff(c_4881,plain,(
    ! [B_390,B_391] :
      ( r2_hidden('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_390),B_391)
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_390)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_391))
      | ~ r1_tarski('#skF_7',B_391) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_38,c_4826])).

tff(c_123,plain,(
    ! [A_79,B_80] :
      ( r2_hidden(k4_tarski('#skF_5'(A_79,B_80),'#skF_6'(A_79,B_80)),'#skF_10')
      | ~ r1_tarski(A_79,'#skF_9')
      | r1_tarski(A_79,B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_116])).

tff(c_2368,plain,(
    ! [A_291,A_292,B_293] :
      ( r1_tarski(A_291,k7_relat_1(A_292,B_293))
      | ~ v1_relat_1(A_291)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_291,k7_relat_1(A_292,B_293)),'#skF_6'(A_291,k7_relat_1(A_292,B_293))),A_292)
      | ~ r2_hidden('#skF_5'(A_291,k7_relat_1(A_292,B_293)),B_293)
      | ~ v1_relat_1(k7_relat_1(A_292,B_293))
      | ~ v1_relat_1(A_292) ) ),
    inference(resolution,[status(thm)],[c_85,c_22])).

tff(c_2414,plain,(
    ! [A_79,B_293] :
      ( ~ r2_hidden('#skF_5'(A_79,k7_relat_1('#skF_10',B_293)),B_293)
      | ~ v1_relat_1(k7_relat_1('#skF_10',B_293))
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski(A_79,'#skF_9')
      | r1_tarski(A_79,k7_relat_1('#skF_10',B_293))
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_123,c_2368])).

tff(c_2445,plain,(
    ! [A_79,B_293] :
      ( ~ r2_hidden('#skF_5'(A_79,k7_relat_1('#skF_10',B_293)),B_293)
      | ~ v1_relat_1(k7_relat_1('#skF_10',B_293))
      | ~ r1_tarski(A_79,'#skF_9')
      | r1_tarski(A_79,k7_relat_1('#skF_10',B_293))
      | ~ v1_relat_1(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2414])).

tff(c_4893,plain,(
    ! [B_391] :
      ( ~ v1_relat_1(k7_relat_1('#skF_10',B_391))
      | ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9')
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_10',B_391))
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_391))
      | ~ r1_tarski('#skF_7',B_391) ) ),
    inference(resolution,[status(thm)],[c_4881,c_2445])).

tff(c_5075,plain,(
    ! [B_396] :
      ( ~ v1_relat_1(k7_relat_1('#skF_10',B_396))
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_10',B_396))
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_396))
      | ~ r1_tarski('#skF_7',B_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_1440,c_4893])).

tff(c_5104,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_5075,c_30])).

tff(c_5146,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5104])).

tff(c_5147,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_5146])).

tff(c_5150,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_5147])).

tff(c_5154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_5150])).

tff(c_5155,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_10','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5146])).

tff(c_5159,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_26,c_5155])).

tff(c_5163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.90/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.61  
% 7.90/2.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.61  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 7.90/2.61  
% 7.90/2.61  %Foreground sorts:
% 7.90/2.61  
% 7.90/2.61  
% 7.90/2.61  %Background operators:
% 7.90/2.61  
% 7.90/2.61  
% 7.90/2.61  %Foreground operators:
% 7.90/2.61  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.90/2.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.90/2.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/2.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.90/2.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.90/2.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.90/2.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.90/2.61  tff('#skF_7', type, '#skF_7': $i).
% 7.90/2.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.90/2.61  tff('#skF_10', type, '#skF_10': $i).
% 7.90/2.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.90/2.61  tff('#skF_9', type, '#skF_9': $i).
% 7.90/2.61  tff('#skF_8', type, '#skF_8': $i).
% 7.90/2.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/2.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.90/2.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.90/2.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/2.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.90/2.61  
% 7.90/2.63  tff(f_71, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 7.90/2.63  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.90/2.63  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 7.90/2.63  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 7.90/2.63  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_relat_1)).
% 7.90/2.63  tff(c_36, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.90/2.63  tff(c_26, plain, (![A_37, B_38]: (v1_relat_1(k7_relat_1(A_37, B_38)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.90/2.63  tff(c_38, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.90/2.63  tff(c_32, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.90/2.63  tff(c_24, plain, (![A_20, B_30]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), A_20) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.90/2.63  tff(c_73, plain, (![D_64, E_65, A_66, B_67]: (r2_hidden(k4_tarski(D_64, E_65), A_66) | ~r2_hidden(k4_tarski(D_64, E_65), k7_relat_1(A_66, B_67)) | ~v1_relat_1(k7_relat_1(A_66, B_67)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.63  tff(c_208, plain, (![A_97, B_98, B_99]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_97, B_98), B_99), '#skF_6'(k7_relat_1(A_97, B_98), B_99)), A_97) | ~v1_relat_1(A_97) | r1_tarski(k7_relat_1(A_97, B_98), B_99) | ~v1_relat_1(k7_relat_1(A_97, B_98)))), inference(resolution, [status(thm)], [c_24, c_73])).
% 7.90/2.63  tff(c_20, plain, (![C_35, D_36, B_30, A_20]: (r2_hidden(k4_tarski(C_35, D_36), B_30) | ~r2_hidden(k4_tarski(C_35, D_36), A_20) | ~r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.90/2.63  tff(c_397, plain, (![A_140, B_141, B_142, B_143]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_140, B_141), B_142), '#skF_6'(k7_relat_1(A_140, B_141), B_142)), B_143) | ~r1_tarski(A_140, B_143) | ~v1_relat_1(A_140) | r1_tarski(k7_relat_1(A_140, B_141), B_142) | ~v1_relat_1(k7_relat_1(A_140, B_141)))), inference(resolution, [status(thm)], [c_208, c_20])).
% 7.90/2.63  tff(c_22, plain, (![A_20, B_30]: (~r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), B_30) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.90/2.63  tff(c_422, plain, (![A_144, B_145, B_146]: (~r1_tarski(A_144, B_145) | ~v1_relat_1(A_144) | r1_tarski(k7_relat_1(A_144, B_146), B_145) | ~v1_relat_1(k7_relat_1(A_144, B_146)))), inference(resolution, [status(thm)], [c_397, c_22])).
% 7.90/2.63  tff(c_30, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_10', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.90/2.63  tff(c_439, plain, (~r1_tarski('#skF_9', k7_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_422, c_30])).
% 7.90/2.63  tff(c_448, plain, (~r1_tarski('#skF_9', k7_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_439])).
% 7.90/2.63  tff(c_449, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_448])).
% 7.90/2.63  tff(c_452, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_449])).
% 7.90/2.63  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_452])).
% 7.90/2.63  tff(c_458, plain, (v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_448])).
% 7.90/2.63  tff(c_226, plain, (![A_97, B_98]: (~v1_relat_1(A_97) | r1_tarski(k7_relat_1(A_97, B_98), A_97) | ~v1_relat_1(k7_relat_1(A_97, B_98)))), inference(resolution, [status(thm)], [c_208, c_22])).
% 7.90/2.63  tff(c_10, plain, (![A_1, B_12, C_13]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_12, C_13), '#skF_2'(A_1, B_12, C_13)), A_1) | r2_hidden(k4_tarski('#skF_3'(A_1, B_12, C_13), '#skF_4'(A_1, B_12, C_13)), C_13) | k7_relat_1(A_1, B_12)=C_13 | ~v1_relat_1(C_13) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.63  tff(c_459, plain, (![A_147, B_148, C_149]: (~r2_hidden(k4_tarski('#skF_1'(A_147, B_148, C_149), '#skF_2'(A_147, B_148, C_149)), C_149) | r2_hidden(k4_tarski('#skF_3'(A_147, B_148, C_149), '#skF_4'(A_147, B_148, C_149)), C_149) | k7_relat_1(A_147, B_148)=C_149 | ~v1_relat_1(C_149) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.63  tff(c_470, plain, (![A_150, B_151]: (r2_hidden(k4_tarski('#skF_3'(A_150, B_151, A_150), '#skF_4'(A_150, B_151, A_150)), A_150) | k7_relat_1(A_150, B_151)=A_150 | ~v1_relat_1(A_150))), inference(resolution, [status(thm)], [c_10, c_459])).
% 7.90/2.63  tff(c_18, plain, (![D_18, B_12, E_19, A_1]: (r2_hidden(D_18, B_12) | ~r2_hidden(k4_tarski(D_18, E_19), k7_relat_1(A_1, B_12)) | ~v1_relat_1(k7_relat_1(A_1, B_12)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.63  tff(c_488, plain, (![A_1, B_12, B_151]: (r2_hidden('#skF_3'(k7_relat_1(A_1, B_12), B_151, k7_relat_1(A_1, B_12)), B_12) | ~v1_relat_1(A_1) | k7_relat_1(k7_relat_1(A_1, B_12), B_151)=k7_relat_1(A_1, B_12) | ~v1_relat_1(k7_relat_1(A_1, B_12)))), inference(resolution, [status(thm)], [c_470, c_18])).
% 7.90/2.63  tff(c_468, plain, (![A_1, B_12]: (r2_hidden(k4_tarski('#skF_3'(A_1, B_12, A_1), '#skF_4'(A_1, B_12, A_1)), A_1) | k7_relat_1(A_1, B_12)=A_1 | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_10, c_459])).
% 7.90/2.63  tff(c_4, plain, (![A_1, B_12, C_13]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_12, C_13), '#skF_2'(A_1, B_12, C_13)), A_1) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_12, C_13), '#skF_4'(A_1, B_12, C_13)), A_1) | ~r2_hidden('#skF_3'(A_1, B_12, C_13), B_12) | k7_relat_1(A_1, B_12)=C_13 | ~v1_relat_1(C_13) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.63  tff(c_888, plain, (![A_226, B_227, C_228]: (~r2_hidden(k4_tarski('#skF_1'(A_226, B_227, C_228), '#skF_2'(A_226, B_227, C_228)), C_228) | ~r2_hidden(k4_tarski('#skF_3'(A_226, B_227, C_228), '#skF_4'(A_226, B_227, C_228)), A_226) | ~r2_hidden('#skF_3'(A_226, B_227, C_228), B_227) | k7_relat_1(A_226, B_227)=C_228 | ~v1_relat_1(C_228) | ~v1_relat_1(A_226))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.63  tff(c_901, plain, (![A_229, B_230]: (~r2_hidden(k4_tarski('#skF_3'(A_229, B_230, A_229), '#skF_4'(A_229, B_230, A_229)), A_229) | ~r2_hidden('#skF_3'(A_229, B_230, A_229), B_230) | k7_relat_1(A_229, B_230)=A_229 | ~v1_relat_1(A_229))), inference(resolution, [status(thm)], [c_4, c_888])).
% 7.90/2.63  tff(c_940, plain, (![A_231, B_232]: (~r2_hidden('#skF_3'(A_231, B_232, A_231), B_232) | k7_relat_1(A_231, B_232)=A_231 | ~v1_relat_1(A_231))), inference(resolution, [status(thm)], [c_468, c_901])).
% 7.90/2.63  tff(c_946, plain, (![A_233, B_234]: (~v1_relat_1(A_233) | k7_relat_1(k7_relat_1(A_233, B_234), B_234)=k7_relat_1(A_233, B_234) | ~v1_relat_1(k7_relat_1(A_233, B_234)))), inference(resolution, [status(thm)], [c_488, c_940])).
% 7.90/2.63  tff(c_948, plain, (~v1_relat_1('#skF_9') | k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7')=k7_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_458, c_946])).
% 7.90/2.63  tff(c_953, plain, (k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7')=k7_relat_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_948])).
% 7.90/2.63  tff(c_228, plain, (![A_104, B_105]: (~v1_relat_1(A_104) | r1_tarski(k7_relat_1(A_104, B_105), A_104) | ~v1_relat_1(k7_relat_1(A_104, B_105)))), inference(resolution, [status(thm)], [c_208, c_22])).
% 7.90/2.63  tff(c_34, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.90/2.63  tff(c_48, plain, (![C_52, D_53, B_54, A_55]: (r2_hidden(k4_tarski(C_52, D_53), B_54) | ~r2_hidden(k4_tarski(C_52, D_53), A_55) | ~r1_tarski(A_55, B_54) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.90/2.63  tff(c_59, plain, (![A_61, B_62, B_63]: (r2_hidden(k4_tarski('#skF_5'(A_61, B_62), '#skF_6'(A_61, B_62)), B_63) | ~r1_tarski(A_61, B_63) | r1_tarski(A_61, B_62) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_24, c_48])).
% 7.90/2.63  tff(c_110, plain, (![A_79, B_80, B_81, B_82]: (r2_hidden(k4_tarski('#skF_5'(A_79, B_80), '#skF_6'(A_79, B_80)), B_81) | ~r1_tarski(B_82, B_81) | ~v1_relat_1(B_82) | ~r1_tarski(A_79, B_82) | r1_tarski(A_79, B_80) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_59, c_20])).
% 7.90/2.63  tff(c_116, plain, (![A_79, B_80]: (r2_hidden(k4_tarski('#skF_5'(A_79, B_80), '#skF_6'(A_79, B_80)), '#skF_10') | ~v1_relat_1('#skF_9') | ~r1_tarski(A_79, '#skF_9') | r1_tarski(A_79, B_80) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_34, c_110])).
% 7.90/2.63  tff(c_125, plain, (![A_83, B_84]: (r2_hidden(k4_tarski('#skF_5'(A_83, B_84), '#skF_6'(A_83, B_84)), '#skF_10') | ~r1_tarski(A_83, '#skF_9') | r1_tarski(A_83, B_84) | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_116])).
% 7.90/2.63  tff(c_137, plain, (![A_85]: (~r1_tarski(A_85, '#skF_9') | r1_tarski(A_85, '#skF_10') | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_125, c_22])).
% 7.90/2.63  tff(c_71, plain, (![A_61, B_62, B_30, B_63]: (r2_hidden(k4_tarski('#skF_5'(A_61, B_62), '#skF_6'(A_61, B_62)), B_30) | ~r1_tarski(B_63, B_30) | ~v1_relat_1(B_63) | ~r1_tarski(A_61, B_63) | r1_tarski(A_61, B_62) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_59, c_20])).
% 7.90/2.63  tff(c_140, plain, (![A_61, B_62, A_85]: (r2_hidden(k4_tarski('#skF_5'(A_61, B_62), '#skF_6'(A_61, B_62)), '#skF_10') | ~r1_tarski(A_61, A_85) | r1_tarski(A_61, B_62) | ~v1_relat_1(A_61) | ~r1_tarski(A_85, '#skF_9') | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_137, c_71])).
% 7.90/2.63  tff(c_689, plain, (![A_194, B_195, B_196]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_194, B_195), B_196), '#skF_6'(k7_relat_1(A_194, B_195), B_196)), '#skF_10') | r1_tarski(k7_relat_1(A_194, B_195), B_196) | ~r1_tarski(A_194, '#skF_9') | ~v1_relat_1(A_194) | ~v1_relat_1(k7_relat_1(A_194, B_195)))), inference(resolution, [status(thm)], [c_228, c_140])).
% 7.90/2.63  tff(c_707, plain, (![A_194, B_195]: (r1_tarski(k7_relat_1(A_194, B_195), '#skF_10') | ~r1_tarski(A_194, '#skF_9') | ~v1_relat_1(A_194) | ~v1_relat_1(k7_relat_1(A_194, B_195)))), inference(resolution, [status(thm)], [c_689, c_22])).
% 7.90/2.63  tff(c_978, plain, (r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_10') | ~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_953, c_707])).
% 7.90/2.63  tff(c_1066, plain, (r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_10') | ~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_953, c_458, c_978])).
% 7.90/2.63  tff(c_1404, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_1066])).
% 7.90/2.63  tff(c_1431, plain, (~v1_relat_1('#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_226, c_1404])).
% 7.90/2.63  tff(c_1438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_38, c_1431])).
% 7.90/2.63  tff(c_1440, plain, (r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_1066])).
% 7.90/2.63  tff(c_28, plain, (![C_41, A_39, B_40]: (r1_tarski(k7_relat_1(C_41, A_39), k7_relat_1(C_41, B_40)) | ~r1_tarski(A_39, B_40) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.90/2.63  tff(c_102, plain, (![A_75, B_76, B_77, A_78]: (r2_hidden('#skF_5'(A_75, B_76), B_77) | ~v1_relat_1(k7_relat_1(A_78, B_77)) | ~v1_relat_1(A_78) | ~r1_tarski(A_75, k7_relat_1(A_78, B_77)) | r1_tarski(A_75, B_76) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_59, c_18])).
% 7.90/2.63  tff(c_109, plain, (![C_41, A_39, B_76, B_40]: (r2_hidden('#skF_5'(k7_relat_1(C_41, A_39), B_76), B_40) | ~v1_relat_1(k7_relat_1(C_41, B_40)) | r1_tarski(k7_relat_1(C_41, A_39), B_76) | ~v1_relat_1(k7_relat_1(C_41, A_39)) | ~r1_tarski(A_39, B_40) | ~v1_relat_1(C_41))), inference(resolution, [status(thm)], [c_28, c_102])).
% 7.90/2.63  tff(c_1021, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_953, c_226])).
% 7.90/2.63  tff(c_1098, plain, (r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_953, c_458, c_1021])).
% 7.90/2.63  tff(c_51, plain, (![A_20, B_30, B_54]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), B_54) | ~r1_tarski(A_20, B_54) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_24, c_48])).
% 7.90/2.63  tff(c_82, plain, (![A_20, B_30, A_66, B_67]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), A_66) | ~v1_relat_1(k7_relat_1(A_66, B_67)) | ~v1_relat_1(A_66) | ~r1_tarski(A_20, k7_relat_1(A_66, B_67)) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_51, c_73])).
% 7.90/2.63  tff(c_1137, plain, (![B_30]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), B_30), '#skF_6'(k7_relat_1('#skF_9', '#skF_7'), B_30)), '#skF_9') | ~v1_relat_1('#skF_9') | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_30) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')))), inference(resolution, [status(thm)], [c_1098, c_82])).
% 7.90/2.63  tff(c_2818, plain, (![B_311]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), B_311), '#skF_6'(k7_relat_1('#skF_9', '#skF_7'), B_311)), '#skF_9') | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_311))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_38, c_1137])).
% 7.90/2.63  tff(c_85, plain, (![D_71, E_72, A_73, B_74]: (r2_hidden(k4_tarski(D_71, E_72), k7_relat_1(A_73, B_74)) | ~r2_hidden(k4_tarski(D_71, E_72), A_73) | ~r2_hidden(D_71, B_74) | ~v1_relat_1(k7_relat_1(A_73, B_74)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/2.63  tff(c_101, plain, (![A_20, A_73, B_74]: (r1_tarski(A_20, k7_relat_1(A_73, B_74)) | ~v1_relat_1(A_20) | ~r2_hidden(k4_tarski('#skF_5'(A_20, k7_relat_1(A_73, B_74)), '#skF_6'(A_20, k7_relat_1(A_73, B_74))), A_73) | ~r2_hidden('#skF_5'(A_20, k7_relat_1(A_73, B_74)), B_74) | ~v1_relat_1(k7_relat_1(A_73, B_74)) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_85, c_22])).
% 7.90/2.63  tff(c_2824, plain, (![B_74]: (~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | ~r2_hidden('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', B_74)), B_74) | ~v1_relat_1(k7_relat_1('#skF_9', B_74)) | ~v1_relat_1('#skF_9') | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', B_74)))), inference(resolution, [status(thm)], [c_2818, c_101])).
% 7.90/2.63  tff(c_4753, plain, (![B_388]: (~r2_hidden('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', B_388)), B_388) | ~v1_relat_1(k7_relat_1('#skF_9', B_388)) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', B_388)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_458, c_2824])).
% 7.90/2.63  tff(c_4765, plain, (![B_40]: (~v1_relat_1(k7_relat_1('#skF_9', B_40)) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', B_40)) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | ~r1_tarski('#skF_7', B_40) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_109, c_4753])).
% 7.90/2.63  tff(c_4782, plain, (![B_389]: (~v1_relat_1(k7_relat_1('#skF_9', B_389)) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', B_389)) | ~r1_tarski('#skF_7', B_389))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_458, c_4765])).
% 7.90/2.63  tff(c_70, plain, (![A_61, B_62, B_12, A_1]: (r2_hidden('#skF_5'(A_61, B_62), B_12) | ~v1_relat_1(k7_relat_1(A_1, B_12)) | ~v1_relat_1(A_1) | ~r1_tarski(A_61, k7_relat_1(A_1, B_12)) | r1_tarski(A_61, B_62) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_59, c_18])).
% 7.90/2.63  tff(c_4826, plain, (![B_62, B_389]: (r2_hidden('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), B_62), B_389) | ~v1_relat_1('#skF_9') | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_62) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1(k7_relat_1('#skF_9', B_389)) | ~r1_tarski('#skF_7', B_389))), inference(resolution, [status(thm)], [c_4782, c_70])).
% 7.90/2.63  tff(c_4881, plain, (![B_390, B_391]: (r2_hidden('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), B_390), B_391) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_390) | ~v1_relat_1(k7_relat_1('#skF_9', B_391)) | ~r1_tarski('#skF_7', B_391))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_38, c_4826])).
% 7.90/2.63  tff(c_123, plain, (![A_79, B_80]: (r2_hidden(k4_tarski('#skF_5'(A_79, B_80), '#skF_6'(A_79, B_80)), '#skF_10') | ~r1_tarski(A_79, '#skF_9') | r1_tarski(A_79, B_80) | ~v1_relat_1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_116])).
% 7.90/2.63  tff(c_2368, plain, (![A_291, A_292, B_293]: (r1_tarski(A_291, k7_relat_1(A_292, B_293)) | ~v1_relat_1(A_291) | ~r2_hidden(k4_tarski('#skF_5'(A_291, k7_relat_1(A_292, B_293)), '#skF_6'(A_291, k7_relat_1(A_292, B_293))), A_292) | ~r2_hidden('#skF_5'(A_291, k7_relat_1(A_292, B_293)), B_293) | ~v1_relat_1(k7_relat_1(A_292, B_293)) | ~v1_relat_1(A_292))), inference(resolution, [status(thm)], [c_85, c_22])).
% 7.90/2.63  tff(c_2414, plain, (![A_79, B_293]: (~r2_hidden('#skF_5'(A_79, k7_relat_1('#skF_10', B_293)), B_293) | ~v1_relat_1(k7_relat_1('#skF_10', B_293)) | ~v1_relat_1('#skF_10') | ~r1_tarski(A_79, '#skF_9') | r1_tarski(A_79, k7_relat_1('#skF_10', B_293)) | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_123, c_2368])).
% 7.90/2.63  tff(c_2445, plain, (![A_79, B_293]: (~r2_hidden('#skF_5'(A_79, k7_relat_1('#skF_10', B_293)), B_293) | ~v1_relat_1(k7_relat_1('#skF_10', B_293)) | ~r1_tarski(A_79, '#skF_9') | r1_tarski(A_79, k7_relat_1('#skF_10', B_293)) | ~v1_relat_1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2414])).
% 7.90/2.63  tff(c_4893, plain, (![B_391]: (~v1_relat_1(k7_relat_1('#skF_10', B_391)) | ~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_10', B_391)) | ~v1_relat_1(k7_relat_1('#skF_9', B_391)) | ~r1_tarski('#skF_7', B_391))), inference(resolution, [status(thm)], [c_4881, c_2445])).
% 7.90/2.63  tff(c_5075, plain, (![B_396]: (~v1_relat_1(k7_relat_1('#skF_10', B_396)) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_10', B_396)) | ~v1_relat_1(k7_relat_1('#skF_9', B_396)) | ~r1_tarski('#skF_7', B_396))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_1440, c_4893])).
% 7.90/2.63  tff(c_5104, plain, (~v1_relat_1(k7_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_8')) | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_5075, c_30])).
% 7.90/2.63  tff(c_5146, plain, (~v1_relat_1(k7_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5104])).
% 7.90/2.63  tff(c_5147, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_8'))), inference(splitLeft, [status(thm)], [c_5146])).
% 7.90/2.63  tff(c_5150, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_5147])).
% 7.90/2.63  tff(c_5154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_5150])).
% 7.90/2.63  tff(c_5155, plain, (~v1_relat_1(k7_relat_1('#skF_10', '#skF_8'))), inference(splitRight, [status(thm)], [c_5146])).
% 7.90/2.63  tff(c_5159, plain, (~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_26, c_5155])).
% 7.90/2.63  tff(c_5163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_5159])).
% 7.90/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.90/2.63  
% 7.90/2.63  Inference rules
% 7.90/2.63  ----------------------
% 7.90/2.63  #Ref     : 0
% 7.90/2.63  #Sup     : 1143
% 7.90/2.63  #Fact    : 0
% 7.90/2.63  #Define  : 0
% 7.90/2.63  #Split   : 7
% 7.90/2.63  #Chain   : 0
% 7.90/2.63  #Close   : 0
% 7.90/2.63  
% 7.90/2.63  Ordering : KBO
% 7.90/2.63  
% 7.90/2.63  Simplification rules
% 7.90/2.63  ----------------------
% 7.90/2.63  #Subsume      : 295
% 7.90/2.63  #Demod        : 986
% 7.90/2.63  #Tautology    : 129
% 7.90/2.63  #SimpNegUnit  : 0
% 7.90/2.63  #BackRed      : 0
% 7.90/2.63  
% 7.90/2.63  #Partial instantiations: 0
% 7.90/2.63  #Strategies tried      : 1
% 7.90/2.63  
% 7.90/2.63  Timing (in seconds)
% 7.90/2.63  ----------------------
% 7.90/2.63  Preprocessing        : 0.29
% 7.90/2.63  Parsing              : 0.15
% 7.90/2.63  CNF conversion       : 0.03
% 7.90/2.63  Main loop            : 1.57
% 7.90/2.63  Inferencing          : 0.41
% 7.90/2.63  Reduction            : 0.41
% 7.90/2.63  Demodulation         : 0.28
% 7.90/2.63  BG Simplification    : 0.05
% 7.90/2.63  Subsumption          : 0.61
% 7.90/2.63  Abstraction          : 0.06
% 7.90/2.63  MUC search           : 0.00
% 7.90/2.63  Cooper               : 0.00
% 7.90/2.63  Total                : 1.90
% 7.90/2.63  Index Insertion      : 0.00
% 7.90/2.63  Index Deletion       : 0.00
% 7.90/2.63  Index Matching       : 0.00
% 7.90/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
