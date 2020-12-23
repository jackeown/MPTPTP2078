%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:54 EST 2020

% Result     : Theorem 13.86s
% Output     : CNFRefutation 13.86s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 456 expanded)
%              Number of leaves         :   22 ( 162 expanded)
%              Depth                    :   18
%              Number of atoms          :  230 (1589 expanded)
%              Number of equality atoms :   15 ( 127 expanded)
%              Maximal formula depth    :   13 (   6 average)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k7_relat_1(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_20,B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_20)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [D_63,E_64,A_65,B_66] :
      ( r2_hidden(k4_tarski(D_63,E_64),A_65)
      | ~ r2_hidden(k4_tarski(D_63,E_64),k7_relat_1(A_65,B_66))
      | ~ v1_relat_1(k7_relat_1(A_65,B_66))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_310,plain,(
    ! [A_103,B_104,B_105] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_103,B_104),B_105),'#skF_6'(k7_relat_1(A_103,B_104),B_105)),A_103)
      | ~ v1_relat_1(A_103)
      | r1_tarski(k7_relat_1(A_103,B_104),B_105)
      | ~ v1_relat_1(k7_relat_1(A_103,B_104)) ) ),
    inference(resolution,[status(thm)],[c_24,c_89])).

tff(c_20,plain,(
    ! [C_35,D_36,B_30,A_20] :
      ( r2_hidden(k4_tarski(C_35,D_36),B_30)
      | ~ r2_hidden(k4_tarski(C_35,D_36),A_20)
      | ~ r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1077,plain,(
    ! [A_192,B_193,B_194,B_195] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_192,B_193),B_194),'#skF_6'(k7_relat_1(A_192,B_193),B_194)),B_195)
      | ~ r1_tarski(A_192,B_195)
      | ~ v1_relat_1(A_192)
      | r1_tarski(k7_relat_1(A_192,B_193),B_194)
      | ~ v1_relat_1(k7_relat_1(A_192,B_193)) ) ),
    inference(resolution,[status(thm)],[c_310,c_20])).

tff(c_22,plain,(
    ! [A_20,B_30] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_30)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1137,plain,(
    ! [A_196,B_197,B_198] :
      ( ~ r1_tarski(A_196,B_197)
      | ~ v1_relat_1(A_196)
      | r1_tarski(k7_relat_1(A_196,B_198),B_197)
      | ~ v1_relat_1(k7_relat_1(A_196,B_198)) ) ),
    inference(resolution,[status(thm)],[c_1077,c_22])).

tff(c_30,plain,(
    ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1159,plain,
    ( ~ r1_tarski('#skF_9',k7_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1137,c_30])).

tff(c_1185,plain,
    ( ~ r1_tarski('#skF_9',k7_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1159])).

tff(c_1199,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1185])).

tff(c_1202,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_1199])).

tff(c_1206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1202])).

tff(c_1208,plain,(
    v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1185])).

tff(c_10,plain,(
    ! [A_1,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_12,C_13),'#skF_2'(A_1,B_12,C_13)),A_1)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_12,C_13),'#skF_4'(A_1,B_12,C_13)),C_13)
      | k7_relat_1(A_1,B_12) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_712,plain,(
    ! [A_125,B_126,C_127] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_125,B_126,C_127),'#skF_2'(A_125,B_126,C_127)),C_127)
      | r2_hidden(k4_tarski('#skF_3'(A_125,B_126,C_127),'#skF_4'(A_125,B_126,C_127)),C_127)
      | k7_relat_1(A_125,B_126) = C_127
      | ~ v1_relat_1(C_127)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_723,plain,(
    ! [A_128,B_129] :
      ( r2_hidden(k4_tarski('#skF_3'(A_128,B_129,A_128),'#skF_4'(A_128,B_129,A_128)),A_128)
      | k7_relat_1(A_128,B_129) = A_128
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_10,c_712])).

tff(c_18,plain,(
    ! [D_18,B_12,E_19,A_1] :
      ( r2_hidden(D_18,B_12)
      | ~ r2_hidden(k4_tarski(D_18,E_19),k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_739,plain,(
    ! [A_1,B_12,B_129] :
      ( r2_hidden('#skF_3'(k7_relat_1(A_1,B_12),B_129,k7_relat_1(A_1,B_12)),B_12)
      | ~ v1_relat_1(A_1)
      | k7_relat_1(k7_relat_1(A_1,B_12),B_129) = k7_relat_1(A_1,B_12)
      | ~ v1_relat_1(k7_relat_1(A_1,B_12)) ) ),
    inference(resolution,[status(thm)],[c_723,c_18])).

tff(c_721,plain,(
    ! [A_1,B_12] :
      ( r2_hidden(k4_tarski('#skF_3'(A_1,B_12,A_1),'#skF_4'(A_1,B_12,A_1)),A_1)
      | k7_relat_1(A_1,B_12) = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_10,c_712])).

tff(c_4,plain,(
    ! [A_1,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_1,B_12,C_13),'#skF_2'(A_1,B_12,C_13)),A_1)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_12,C_13),'#skF_4'(A_1,B_12,C_13)),A_1)
      | ~ r2_hidden('#skF_3'(A_1,B_12,C_13),B_12)
      | k7_relat_1(A_1,B_12) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1186,plain,(
    ! [A_199,B_200,C_201] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_199,B_200,C_201),'#skF_2'(A_199,B_200,C_201)),C_201)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_199,B_200,C_201),'#skF_4'(A_199,B_200,C_201)),A_199)
      | ~ r2_hidden('#skF_3'(A_199,B_200,C_201),B_200)
      | k7_relat_1(A_199,B_200) = C_201
      | ~ v1_relat_1(C_201)
      | ~ v1_relat_1(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1247,plain,(
    ! [A_207,B_208] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_207,B_208,A_207),'#skF_4'(A_207,B_208,A_207)),A_207)
      | ~ r2_hidden('#skF_3'(A_207,B_208,A_207),B_208)
      | k7_relat_1(A_207,B_208) = A_207
      | ~ v1_relat_1(A_207) ) ),
    inference(resolution,[status(thm)],[c_4,c_1186])).

tff(c_1269,plain,(
    ! [A_209,B_210] :
      ( ~ r2_hidden('#skF_3'(A_209,B_210,A_209),B_210)
      | k7_relat_1(A_209,B_210) = A_209
      | ~ v1_relat_1(A_209) ) ),
    inference(resolution,[status(thm)],[c_721,c_1247])).

tff(c_1275,plain,(
    ! [A_211,B_212] :
      ( ~ v1_relat_1(A_211)
      | k7_relat_1(k7_relat_1(A_211,B_212),B_212) = k7_relat_1(A_211,B_212)
      | ~ v1_relat_1(k7_relat_1(A_211,B_212)) ) ),
    inference(resolution,[status(thm)],[c_739,c_1269])).

tff(c_1277,plain,
    ( ~ v1_relat_1('#skF_9')
    | k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7') = k7_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_1208,c_1275])).

tff(c_1292,plain,(
    k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7') = k7_relat_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1277])).

tff(c_346,plain,(
    ! [A_103,B_104] :
      ( ~ v1_relat_1(A_103)
      | r1_tarski(k7_relat_1(A_103,B_104),A_103)
      | ~ v1_relat_1(k7_relat_1(A_103,B_104)) ) ),
    inference(resolution,[status(thm)],[c_310,c_22])).

tff(c_1371,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
    | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_346])).

tff(c_1456,plain,(
    r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_1292,c_1208,c_1371])).

tff(c_62,plain,(
    ! [C_52,D_53,B_54,A_55] :
      ( r2_hidden(k4_tarski(C_52,D_53),B_54)
      | ~ r2_hidden(k4_tarski(C_52,D_53),A_55)
      | ~ r1_tarski(A_55,B_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_20,B_30,B_54] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_54)
      | ~ r1_tarski(A_20,B_54)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_24,c_62])).

tff(c_101,plain,(
    ! [A_20,B_30,A_65,B_66] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_65)
      | ~ v1_relat_1(k7_relat_1(A_65,B_66))
      | ~ v1_relat_1(A_65)
      | ~ r1_tarski(A_20,k7_relat_1(A_65,B_66))
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_65,c_89])).

tff(c_1499,plain,(
    ! [B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_30),'#skF_6'(k7_relat_1('#skF_9','#skF_7'),B_30)),'#skF_9')
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_30)
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1456,c_101])).

tff(c_3139,plain,(
    ! [B_282] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_282),'#skF_6'(k7_relat_1('#skF_9','#skF_7'),B_282)),'#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_34,c_1499])).

tff(c_3157,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
    | r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_3139,c_22])).

tff(c_3173,plain,(
    r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_3157])).

tff(c_66,plain,(
    ! [D_56,B_57,E_58,A_59] :
      ( r2_hidden(D_56,B_57)
      | ~ r2_hidden(k4_tarski(D_56,E_58),k7_relat_1(A_59,B_57))
      | ~ v1_relat_1(k7_relat_1(A_59,B_57))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    ! [A_59,B_57,B_30] :
      ( r2_hidden('#skF_5'(k7_relat_1(A_59,B_57),B_30),B_57)
      | ~ v1_relat_1(A_59)
      | r1_tarski(k7_relat_1(A_59,B_57),B_30)
      | ~ v1_relat_1(k7_relat_1(A_59,B_57)) ) ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_102,plain,(
    ! [A_65,B_66,B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_65,B_66),B_30),'#skF_6'(k7_relat_1(A_65,B_66),B_30)),A_65)
      | ~ v1_relat_1(A_65)
      | r1_tarski(k7_relat_1(A_65,B_66),B_30)
      | ~ v1_relat_1(k7_relat_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_24,c_89])).

tff(c_32,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [D_18,E_19,A_1,B_12] :
      ( r2_hidden(k4_tarski(D_18,E_19),k7_relat_1(A_1,B_12))
      | ~ r2_hidden(k4_tarski(D_18,E_19),A_1)
      | ~ r2_hidden(D_18,B_12)
      | ~ v1_relat_1(k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [C_41,A_39,B_40] :
      ( k7_relat_1(k7_relat_1(C_41,A_39),B_40) = k7_relat_1(C_41,A_39)
      | ~ r1_tarski(A_39,B_40)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_652,plain,(
    ! [B_118,A_116,D_120,E_117,C_119] :
      ( r2_hidden(D_120,B_118)
      | ~ r2_hidden(k4_tarski(D_120,E_117),k7_relat_1(C_119,A_116))
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(C_119,A_116),B_118))
      | ~ v1_relat_1(k7_relat_1(C_119,A_116))
      | ~ r1_tarski(A_116,B_118)
      | ~ v1_relat_1(C_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_66])).

tff(c_853,plain,(
    ! [D_149,B_152,A_153,E_150,B_151] :
      ( r2_hidden(D_149,B_152)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1(A_153,B_151),B_152))
      | ~ r1_tarski(B_151,B_152)
      | ~ r2_hidden(k4_tarski(D_149,E_150),A_153)
      | ~ r2_hidden(D_149,B_151)
      | ~ v1_relat_1(k7_relat_1(A_153,B_151))
      | ~ v1_relat_1(A_153) ) ),
    inference(resolution,[status(thm)],[c_14,c_652])).

tff(c_878,plain,(
    ! [E_155,D_158,B_156,A_157,B_154] :
      ( r2_hidden(D_158,B_154)
      | ~ r1_tarski(B_156,B_154)
      | ~ r2_hidden(k4_tarski(D_158,E_155),A_157)
      | ~ r2_hidden(D_158,B_156)
      | ~ v1_relat_1(A_157)
      | ~ v1_relat_1(k7_relat_1(A_157,B_156)) ) ),
    inference(resolution,[status(thm)],[c_26,c_853])).

tff(c_891,plain,(
    ! [D_159,E_160,A_161] :
      ( r2_hidden(D_159,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_159,E_160),A_161)
      | ~ r2_hidden(D_159,'#skF_7')
      | ~ v1_relat_1(A_161)
      | ~ v1_relat_1(k7_relat_1(A_161,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_32,c_878])).

tff(c_1209,plain,(
    ! [A_202,B_203,B_204] :
      ( r2_hidden('#skF_5'(k7_relat_1(A_202,B_203),B_204),'#skF_8')
      | ~ r2_hidden('#skF_5'(k7_relat_1(A_202,B_203),B_204),'#skF_7')
      | ~ v1_relat_1(k7_relat_1(A_202,'#skF_7'))
      | ~ v1_relat_1(A_202)
      | r1_tarski(k7_relat_1(A_202,B_203),B_204)
      | ~ v1_relat_1(k7_relat_1(A_202,B_203)) ) ),
    inference(resolution,[status(thm)],[c_102,c_891])).

tff(c_1234,plain,(
    ! [A_59,B_30] :
      ( r2_hidden('#skF_5'(k7_relat_1(A_59,'#skF_7'),B_30),'#skF_8')
      | ~ v1_relat_1(A_59)
      | r1_tarski(k7_relat_1(A_59,'#skF_7'),B_30)
      | ~ v1_relat_1(k7_relat_1(A_59,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_74,c_1209])).

tff(c_1329,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_30),'#skF_8')
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | r1_tarski(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7'),B_30)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_1234])).

tff(c_1426,plain,(
    ! [B_30] :
      ( r2_hidden('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_30),'#skF_8')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_1292,c_1292,c_1208,c_1329])).

tff(c_107,plain,(
    ! [D_70,E_71,A_72,B_73] :
      ( r2_hidden(k4_tarski(D_70,E_71),k7_relat_1(A_72,B_73))
      | ~ r2_hidden(k4_tarski(D_70,E_71),A_72)
      | ~ r2_hidden(D_70,B_73)
      | ~ v1_relat_1(k7_relat_1(A_72,B_73))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2454,plain,(
    ! [A_252,A_253,B_254] :
      ( r1_tarski(A_252,k7_relat_1(A_253,B_254))
      | ~ v1_relat_1(A_252)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_252,k7_relat_1(A_253,B_254)),'#skF_6'(A_252,k7_relat_1(A_253,B_254))),A_253)
      | ~ r2_hidden('#skF_5'(A_252,k7_relat_1(A_253,B_254)),B_254)
      | ~ v1_relat_1(k7_relat_1(A_253,B_254))
      | ~ v1_relat_1(A_253) ) ),
    inference(resolution,[status(thm)],[c_107,c_22])).

tff(c_21009,plain,(
    ! [A_479,B_480,B_481] :
      ( ~ r2_hidden('#skF_5'(A_479,k7_relat_1(B_480,B_481)),B_481)
      | ~ v1_relat_1(k7_relat_1(B_480,B_481))
      | ~ v1_relat_1(B_480)
      | ~ r1_tarski(A_479,B_480)
      | r1_tarski(A_479,k7_relat_1(B_480,B_481))
      | ~ v1_relat_1(A_479) ) ),
    inference(resolution,[status(thm)],[c_65,c_2454])).

tff(c_21081,plain,(
    ! [B_480] :
      ( ~ v1_relat_1(k7_relat_1(B_480,'#skF_8'))
      | ~ v1_relat_1(B_480)
      | ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_480)
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1(B_480,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1426,c_21009])).

tff(c_21618,plain,(
    ! [B_487] :
      ( ~ v1_relat_1(k7_relat_1(B_487,'#skF_8'))
      | ~ v1_relat_1(B_487)
      | ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_487)
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1(B_487,'#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_21081])).

tff(c_21647,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
    | ~ v1_relat_1('#skF_9')
    | ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_21618,c_30])).

tff(c_21766,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3173,c_34,c_21647])).

tff(c_21794,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_21766])).

tff(c_21798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_21794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 16:02:07 EST 2020
% 0.16/0.32  % CPUTime    : 
% 0.16/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.86/5.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.86/5.62  
% 13.86/5.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.86/5.62  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5
% 13.86/5.62  
% 13.86/5.62  %Foreground sorts:
% 13.86/5.62  
% 13.86/5.62  
% 13.86/5.62  %Background operators:
% 13.86/5.62  
% 13.86/5.62  
% 13.86/5.62  %Foreground operators:
% 13.86/5.62  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 13.86/5.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.86/5.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.86/5.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.86/5.62  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.86/5.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.86/5.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 13.86/5.62  tff('#skF_7', type, '#skF_7': $i).
% 13.86/5.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.86/5.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.86/5.62  tff('#skF_9', type, '#skF_9': $i).
% 13.86/5.62  tff('#skF_8', type, '#skF_8': $i).
% 13.86/5.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.86/5.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.86/5.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.86/5.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.86/5.62  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 13.86/5.62  
% 13.86/5.64  tff(f_66, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 13.86/5.64  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 13.86/5.64  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 13.86/5.64  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 13.86/5.64  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 13.86/5.64  tff(c_34, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.86/5.64  tff(c_26, plain, (![A_37, B_38]: (v1_relat_1(k7_relat_1(A_37, B_38)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.86/5.64  tff(c_24, plain, (![A_20, B_30]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), A_20) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.86/5.64  tff(c_89, plain, (![D_63, E_64, A_65, B_66]: (r2_hidden(k4_tarski(D_63, E_64), A_65) | ~r2_hidden(k4_tarski(D_63, E_64), k7_relat_1(A_65, B_66)) | ~v1_relat_1(k7_relat_1(A_65, B_66)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_310, plain, (![A_103, B_104, B_105]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_103, B_104), B_105), '#skF_6'(k7_relat_1(A_103, B_104), B_105)), A_103) | ~v1_relat_1(A_103) | r1_tarski(k7_relat_1(A_103, B_104), B_105) | ~v1_relat_1(k7_relat_1(A_103, B_104)))), inference(resolution, [status(thm)], [c_24, c_89])).
% 13.86/5.64  tff(c_20, plain, (![C_35, D_36, B_30, A_20]: (r2_hidden(k4_tarski(C_35, D_36), B_30) | ~r2_hidden(k4_tarski(C_35, D_36), A_20) | ~r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.86/5.64  tff(c_1077, plain, (![A_192, B_193, B_194, B_195]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_192, B_193), B_194), '#skF_6'(k7_relat_1(A_192, B_193), B_194)), B_195) | ~r1_tarski(A_192, B_195) | ~v1_relat_1(A_192) | r1_tarski(k7_relat_1(A_192, B_193), B_194) | ~v1_relat_1(k7_relat_1(A_192, B_193)))), inference(resolution, [status(thm)], [c_310, c_20])).
% 13.86/5.64  tff(c_22, plain, (![A_20, B_30]: (~r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), B_30) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.86/5.64  tff(c_1137, plain, (![A_196, B_197, B_198]: (~r1_tarski(A_196, B_197) | ~v1_relat_1(A_196) | r1_tarski(k7_relat_1(A_196, B_198), B_197) | ~v1_relat_1(k7_relat_1(A_196, B_198)))), inference(resolution, [status(thm)], [c_1077, c_22])).
% 13.86/5.64  tff(c_30, plain, (~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.86/5.64  tff(c_1159, plain, (~r1_tarski('#skF_9', k7_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(resolution, [status(thm)], [c_1137, c_30])).
% 13.86/5.64  tff(c_1185, plain, (~r1_tarski('#skF_9', k7_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1159])).
% 13.86/5.64  tff(c_1199, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1185])).
% 13.86/5.64  tff(c_1202, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_1199])).
% 13.86/5.64  tff(c_1206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1202])).
% 13.86/5.64  tff(c_1208, plain, (v1_relat_1(k7_relat_1('#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_1185])).
% 13.86/5.64  tff(c_10, plain, (![A_1, B_12, C_13]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_12, C_13), '#skF_2'(A_1, B_12, C_13)), A_1) | r2_hidden(k4_tarski('#skF_3'(A_1, B_12, C_13), '#skF_4'(A_1, B_12, C_13)), C_13) | k7_relat_1(A_1, B_12)=C_13 | ~v1_relat_1(C_13) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_712, plain, (![A_125, B_126, C_127]: (~r2_hidden(k4_tarski('#skF_1'(A_125, B_126, C_127), '#skF_2'(A_125, B_126, C_127)), C_127) | r2_hidden(k4_tarski('#skF_3'(A_125, B_126, C_127), '#skF_4'(A_125, B_126, C_127)), C_127) | k7_relat_1(A_125, B_126)=C_127 | ~v1_relat_1(C_127) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_723, plain, (![A_128, B_129]: (r2_hidden(k4_tarski('#skF_3'(A_128, B_129, A_128), '#skF_4'(A_128, B_129, A_128)), A_128) | k7_relat_1(A_128, B_129)=A_128 | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_10, c_712])).
% 13.86/5.64  tff(c_18, plain, (![D_18, B_12, E_19, A_1]: (r2_hidden(D_18, B_12) | ~r2_hidden(k4_tarski(D_18, E_19), k7_relat_1(A_1, B_12)) | ~v1_relat_1(k7_relat_1(A_1, B_12)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_739, plain, (![A_1, B_12, B_129]: (r2_hidden('#skF_3'(k7_relat_1(A_1, B_12), B_129, k7_relat_1(A_1, B_12)), B_12) | ~v1_relat_1(A_1) | k7_relat_1(k7_relat_1(A_1, B_12), B_129)=k7_relat_1(A_1, B_12) | ~v1_relat_1(k7_relat_1(A_1, B_12)))), inference(resolution, [status(thm)], [c_723, c_18])).
% 13.86/5.64  tff(c_721, plain, (![A_1, B_12]: (r2_hidden(k4_tarski('#skF_3'(A_1, B_12, A_1), '#skF_4'(A_1, B_12, A_1)), A_1) | k7_relat_1(A_1, B_12)=A_1 | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_10, c_712])).
% 13.86/5.64  tff(c_4, plain, (![A_1, B_12, C_13]: (r2_hidden(k4_tarski('#skF_1'(A_1, B_12, C_13), '#skF_2'(A_1, B_12, C_13)), A_1) | ~r2_hidden(k4_tarski('#skF_3'(A_1, B_12, C_13), '#skF_4'(A_1, B_12, C_13)), A_1) | ~r2_hidden('#skF_3'(A_1, B_12, C_13), B_12) | k7_relat_1(A_1, B_12)=C_13 | ~v1_relat_1(C_13) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_1186, plain, (![A_199, B_200, C_201]: (~r2_hidden(k4_tarski('#skF_1'(A_199, B_200, C_201), '#skF_2'(A_199, B_200, C_201)), C_201) | ~r2_hidden(k4_tarski('#skF_3'(A_199, B_200, C_201), '#skF_4'(A_199, B_200, C_201)), A_199) | ~r2_hidden('#skF_3'(A_199, B_200, C_201), B_200) | k7_relat_1(A_199, B_200)=C_201 | ~v1_relat_1(C_201) | ~v1_relat_1(A_199))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_1247, plain, (![A_207, B_208]: (~r2_hidden(k4_tarski('#skF_3'(A_207, B_208, A_207), '#skF_4'(A_207, B_208, A_207)), A_207) | ~r2_hidden('#skF_3'(A_207, B_208, A_207), B_208) | k7_relat_1(A_207, B_208)=A_207 | ~v1_relat_1(A_207))), inference(resolution, [status(thm)], [c_4, c_1186])).
% 13.86/5.64  tff(c_1269, plain, (![A_209, B_210]: (~r2_hidden('#skF_3'(A_209, B_210, A_209), B_210) | k7_relat_1(A_209, B_210)=A_209 | ~v1_relat_1(A_209))), inference(resolution, [status(thm)], [c_721, c_1247])).
% 13.86/5.64  tff(c_1275, plain, (![A_211, B_212]: (~v1_relat_1(A_211) | k7_relat_1(k7_relat_1(A_211, B_212), B_212)=k7_relat_1(A_211, B_212) | ~v1_relat_1(k7_relat_1(A_211, B_212)))), inference(resolution, [status(thm)], [c_739, c_1269])).
% 13.86/5.64  tff(c_1277, plain, (~v1_relat_1('#skF_9') | k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7')=k7_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_1208, c_1275])).
% 13.86/5.64  tff(c_1292, plain, (k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7')=k7_relat_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1277])).
% 13.86/5.64  tff(c_346, plain, (![A_103, B_104]: (~v1_relat_1(A_103) | r1_tarski(k7_relat_1(A_103, B_104), A_103) | ~v1_relat_1(k7_relat_1(A_103, B_104)))), inference(resolution, [status(thm)], [c_310, c_22])).
% 13.86/5.64  tff(c_1371, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_346])).
% 13.86/5.64  tff(c_1456, plain, (r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_1292, c_1208, c_1371])).
% 13.86/5.64  tff(c_62, plain, (![C_52, D_53, B_54, A_55]: (r2_hidden(k4_tarski(C_52, D_53), B_54) | ~r2_hidden(k4_tarski(C_52, D_53), A_55) | ~r1_tarski(A_55, B_54) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.86/5.64  tff(c_65, plain, (![A_20, B_30, B_54]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), B_54) | ~r1_tarski(A_20, B_54) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_24, c_62])).
% 13.86/5.64  tff(c_101, plain, (![A_20, B_30, A_65, B_66]: (r2_hidden(k4_tarski('#skF_5'(A_20, B_30), '#skF_6'(A_20, B_30)), A_65) | ~v1_relat_1(k7_relat_1(A_65, B_66)) | ~v1_relat_1(A_65) | ~r1_tarski(A_20, k7_relat_1(A_65, B_66)) | r1_tarski(A_20, B_30) | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_65, c_89])).
% 13.86/5.64  tff(c_1499, plain, (![B_30]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), B_30), '#skF_6'(k7_relat_1('#skF_9', '#skF_7'), B_30)), '#skF_9') | ~v1_relat_1('#skF_9') | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_30) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')))), inference(resolution, [status(thm)], [c_1456, c_101])).
% 13.86/5.64  tff(c_3139, plain, (![B_282]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), B_282), '#skF_6'(k7_relat_1('#skF_9', '#skF_7'), B_282)), '#skF_9') | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_282))), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_34, c_1499])).
% 13.86/5.64  tff(c_3157, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_3139, c_22])).
% 13.86/5.64  tff(c_3173, plain, (r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_3157])).
% 13.86/5.64  tff(c_66, plain, (![D_56, B_57, E_58, A_59]: (r2_hidden(D_56, B_57) | ~r2_hidden(k4_tarski(D_56, E_58), k7_relat_1(A_59, B_57)) | ~v1_relat_1(k7_relat_1(A_59, B_57)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_74, plain, (![A_59, B_57, B_30]: (r2_hidden('#skF_5'(k7_relat_1(A_59, B_57), B_30), B_57) | ~v1_relat_1(A_59) | r1_tarski(k7_relat_1(A_59, B_57), B_30) | ~v1_relat_1(k7_relat_1(A_59, B_57)))), inference(resolution, [status(thm)], [c_24, c_66])).
% 13.86/5.64  tff(c_102, plain, (![A_65, B_66, B_30]: (r2_hidden(k4_tarski('#skF_5'(k7_relat_1(A_65, B_66), B_30), '#skF_6'(k7_relat_1(A_65, B_66), B_30)), A_65) | ~v1_relat_1(A_65) | r1_tarski(k7_relat_1(A_65, B_66), B_30) | ~v1_relat_1(k7_relat_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_24, c_89])).
% 13.86/5.64  tff(c_32, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_66])).
% 13.86/5.64  tff(c_14, plain, (![D_18, E_19, A_1, B_12]: (r2_hidden(k4_tarski(D_18, E_19), k7_relat_1(A_1, B_12)) | ~r2_hidden(k4_tarski(D_18, E_19), A_1) | ~r2_hidden(D_18, B_12) | ~v1_relat_1(k7_relat_1(A_1, B_12)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_28, plain, (![C_41, A_39, B_40]: (k7_relat_1(k7_relat_1(C_41, A_39), B_40)=k7_relat_1(C_41, A_39) | ~r1_tarski(A_39, B_40) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.86/5.64  tff(c_652, plain, (![B_118, A_116, D_120, E_117, C_119]: (r2_hidden(D_120, B_118) | ~r2_hidden(k4_tarski(D_120, E_117), k7_relat_1(C_119, A_116)) | ~v1_relat_1(k7_relat_1(k7_relat_1(C_119, A_116), B_118)) | ~v1_relat_1(k7_relat_1(C_119, A_116)) | ~r1_tarski(A_116, B_118) | ~v1_relat_1(C_119))), inference(superposition, [status(thm), theory('equality')], [c_28, c_66])).
% 13.86/5.64  tff(c_853, plain, (![D_149, B_152, A_153, E_150, B_151]: (r2_hidden(D_149, B_152) | ~v1_relat_1(k7_relat_1(k7_relat_1(A_153, B_151), B_152)) | ~r1_tarski(B_151, B_152) | ~r2_hidden(k4_tarski(D_149, E_150), A_153) | ~r2_hidden(D_149, B_151) | ~v1_relat_1(k7_relat_1(A_153, B_151)) | ~v1_relat_1(A_153))), inference(resolution, [status(thm)], [c_14, c_652])).
% 13.86/5.64  tff(c_878, plain, (![E_155, D_158, B_156, A_157, B_154]: (r2_hidden(D_158, B_154) | ~r1_tarski(B_156, B_154) | ~r2_hidden(k4_tarski(D_158, E_155), A_157) | ~r2_hidden(D_158, B_156) | ~v1_relat_1(A_157) | ~v1_relat_1(k7_relat_1(A_157, B_156)))), inference(resolution, [status(thm)], [c_26, c_853])).
% 13.86/5.64  tff(c_891, plain, (![D_159, E_160, A_161]: (r2_hidden(D_159, '#skF_8') | ~r2_hidden(k4_tarski(D_159, E_160), A_161) | ~r2_hidden(D_159, '#skF_7') | ~v1_relat_1(A_161) | ~v1_relat_1(k7_relat_1(A_161, '#skF_7')))), inference(resolution, [status(thm)], [c_32, c_878])).
% 13.86/5.64  tff(c_1209, plain, (![A_202, B_203, B_204]: (r2_hidden('#skF_5'(k7_relat_1(A_202, B_203), B_204), '#skF_8') | ~r2_hidden('#skF_5'(k7_relat_1(A_202, B_203), B_204), '#skF_7') | ~v1_relat_1(k7_relat_1(A_202, '#skF_7')) | ~v1_relat_1(A_202) | r1_tarski(k7_relat_1(A_202, B_203), B_204) | ~v1_relat_1(k7_relat_1(A_202, B_203)))), inference(resolution, [status(thm)], [c_102, c_891])).
% 13.86/5.64  tff(c_1234, plain, (![A_59, B_30]: (r2_hidden('#skF_5'(k7_relat_1(A_59, '#skF_7'), B_30), '#skF_8') | ~v1_relat_1(A_59) | r1_tarski(k7_relat_1(A_59, '#skF_7'), B_30) | ~v1_relat_1(k7_relat_1(A_59, '#skF_7')))), inference(resolution, [status(thm)], [c_74, c_1209])).
% 13.86/5.64  tff(c_1329, plain, (![B_30]: (r2_hidden('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), B_30), '#skF_8') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | r1_tarski(k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7'), B_30) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_9', '#skF_7'), '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_1292, c_1234])).
% 13.86/5.64  tff(c_1426, plain, (![B_30]: (r2_hidden('#skF_5'(k7_relat_1('#skF_9', '#skF_7'), B_30), '#skF_8') | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_30))), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_1292, c_1292, c_1208, c_1329])).
% 13.86/5.64  tff(c_107, plain, (![D_70, E_71, A_72, B_73]: (r2_hidden(k4_tarski(D_70, E_71), k7_relat_1(A_72, B_73)) | ~r2_hidden(k4_tarski(D_70, E_71), A_72) | ~r2_hidden(D_70, B_73) | ~v1_relat_1(k7_relat_1(A_72, B_73)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.86/5.64  tff(c_2454, plain, (![A_252, A_253, B_254]: (r1_tarski(A_252, k7_relat_1(A_253, B_254)) | ~v1_relat_1(A_252) | ~r2_hidden(k4_tarski('#skF_5'(A_252, k7_relat_1(A_253, B_254)), '#skF_6'(A_252, k7_relat_1(A_253, B_254))), A_253) | ~r2_hidden('#skF_5'(A_252, k7_relat_1(A_253, B_254)), B_254) | ~v1_relat_1(k7_relat_1(A_253, B_254)) | ~v1_relat_1(A_253))), inference(resolution, [status(thm)], [c_107, c_22])).
% 13.86/5.64  tff(c_21009, plain, (![A_479, B_480, B_481]: (~r2_hidden('#skF_5'(A_479, k7_relat_1(B_480, B_481)), B_481) | ~v1_relat_1(k7_relat_1(B_480, B_481)) | ~v1_relat_1(B_480) | ~r1_tarski(A_479, B_480) | r1_tarski(A_479, k7_relat_1(B_480, B_481)) | ~v1_relat_1(A_479))), inference(resolution, [status(thm)], [c_65, c_2454])).
% 13.86/5.64  tff(c_21081, plain, (![B_480]: (~v1_relat_1(k7_relat_1(B_480, '#skF_8')) | ~v1_relat_1(B_480) | ~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_480) | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_7')) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1(B_480, '#skF_8')))), inference(resolution, [status(thm)], [c_1426, c_21009])).
% 13.86/5.64  tff(c_21618, plain, (![B_487]: (~v1_relat_1(k7_relat_1(B_487, '#skF_8')) | ~v1_relat_1(B_487) | ~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), B_487) | r1_tarski(k7_relat_1('#skF_9', '#skF_7'), k7_relat_1(B_487, '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_21081])).
% 13.86/5.64  tff(c_21647, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9') | ~r1_tarski(k7_relat_1('#skF_9', '#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_21618, c_30])).
% 13.86/5.64  tff(c_21766, plain, (~v1_relat_1(k7_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3173, c_34, c_21647])).
% 13.86/5.64  tff(c_21794, plain, (~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26, c_21766])).
% 13.86/5.64  tff(c_21798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_21794])).
% 13.86/5.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.86/5.64  
% 13.86/5.64  Inference rules
% 13.86/5.64  ----------------------
% 13.86/5.64  #Ref     : 0
% 13.86/5.64  #Sup     : 5323
% 13.86/5.64  #Fact    : 0
% 13.86/5.64  #Define  : 0
% 13.86/5.64  #Split   : 11
% 13.86/5.64  #Chain   : 0
% 13.86/5.64  #Close   : 0
% 13.86/5.64  
% 13.86/5.64  Ordering : KBO
% 13.86/5.64  
% 13.86/5.64  Simplification rules
% 13.86/5.64  ----------------------
% 13.86/5.64  #Subsume      : 1562
% 13.86/5.64  #Demod        : 5042
% 13.86/5.64  #Tautology    : 516
% 13.86/5.64  #SimpNegUnit  : 1
% 13.86/5.64  #BackRed      : 5
% 13.86/5.64  
% 13.86/5.64  #Partial instantiations: 0
% 13.86/5.64  #Strategies tried      : 1
% 13.86/5.64  
% 13.86/5.64  Timing (in seconds)
% 13.86/5.64  ----------------------
% 13.86/5.64  Preprocessing        : 0.30
% 13.86/5.64  Parsing              : 0.16
% 13.86/5.64  CNF conversion       : 0.03
% 13.86/5.64  Main loop            : 4.60
% 13.86/5.64  Inferencing          : 1.02
% 13.86/5.64  Reduction            : 1.20
% 13.86/5.64  Demodulation         : 0.85
% 13.86/5.64  BG Simplification    : 0.15
% 13.86/5.64  Subsumption          : 2.04
% 13.86/5.64  Abstraction          : 0.20
% 13.86/5.64  MUC search           : 0.00
% 13.86/5.64  Cooper               : 0.00
% 13.86/5.64  Total                : 4.93
% 13.86/5.64  Index Insertion      : 0.00
% 13.86/5.64  Index Deletion       : 0.00
% 13.86/5.64  Index Matching       : 0.00
% 13.86/5.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
