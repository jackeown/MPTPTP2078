%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0569+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:31 EST 2020

% Result     : Theorem 9.17s
% Output     : CNFRefutation 9.17s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 221 expanded)
%              Number of leaves         :   25 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  147 ( 580 expanded)
%              Number of equality atoms :   36 ( 112 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_30,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_6'(A_30,B_31),B_31)
      | r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_6'(A_30,B_31),A_30)
      | r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_552,plain,(
    ! [A_121,B_122,C_123] :
      ( ~ r1_xboole_0(A_121,B_122)
      | ~ r2_hidden(C_123,B_122)
      | ~ r2_hidden(C_123,A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_556,plain,(
    ! [C_124,B_125,A_126] :
      ( ~ r2_hidden(C_124,B_125)
      | ~ r2_hidden(C_124,A_126)
      | k3_xboole_0(A_126,B_125) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_552])).

tff(c_729,plain,(
    ! [A_160,B_161,A_162] :
      ( ~ r2_hidden('#skF_6'(A_160,B_161),A_162)
      | k3_xboole_0(A_162,A_160) != k1_xboole_0
      | r1_xboole_0(A_160,B_161) ) ),
    inference(resolution,[status(thm)],[c_32,c_556])).

tff(c_739,plain,(
    ! [B_163,A_164] :
      ( k3_xboole_0(B_163,A_164) != k1_xboole_0
      | r1_xboole_0(A_164,B_163) ) ),
    inference(resolution,[status(thm)],[c_30,c_729])).

tff(c_36,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7')
    | k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_59,plain,(
    k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden('#skF_5'(A_24,B_25,C_26),B_25)
      | ~ r2_hidden(A_24,k10_relat_1(C_26,B_25))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_371,plain,(
    ! [A_102,B_103,C_104] :
      ( r2_hidden('#skF_5'(A_102,B_103,C_104),k2_relat_1(C_104))
      | ~ r2_hidden(A_102,k10_relat_1(C_104,B_103))
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_42])).

tff(c_70,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,B_45)
      | ~ r2_hidden(C_46,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_75,plain,(
    ! [C_46] :
      ( ~ r2_hidden(C_46,'#skF_7')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_60,c_70])).

tff(c_383,plain,(
    ! [A_102,B_103] :
      ( ~ r2_hidden('#skF_5'(A_102,B_103,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_102,k10_relat_1('#skF_8',B_103))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_371,c_75])).

tff(c_392,plain,(
    ! [A_106,B_107] :
      ( ~ r2_hidden('#skF_5'(A_106,B_107,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_106,k10_relat_1('#skF_8',B_107)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_383])).

tff(c_396,plain,(
    ! [A_24] :
      ( ~ r2_hidden(A_24,k10_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_22,c_392])).

tff(c_400,plain,(
    ! [A_108] : ~ r2_hidden(A_108,k10_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_396])).

tff(c_426,plain,(
    ! [A_109] : r1_xboole_0(A_109,k10_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_30,c_400])).

tff(c_14,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_505,plain,(
    ! [A_115] : k3_xboole_0(A_115,k10_relat_1('#skF_8','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_426,c_14])).

tff(c_18,plain,(
    ! [A_22] : k3_xboole_0(A_22,A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_519,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_18])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_519])).

tff(c_538,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_749,plain,(
    k3_xboole_0('#skF_7',k2_relat_1('#skF_8')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_739,c_538])).

tff(c_26,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden('#skF_5'(A_24,B_25,C_26),k2_relat_1(C_26))
      | ~ r2_hidden(A_24,k10_relat_1(C_26,B_25))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_567,plain,(
    ! [A_130,B_131,A_132] :
      ( ~ r2_hidden('#skF_6'(A_130,B_131),A_132)
      | k3_xboole_0(A_132,B_131) != k1_xboole_0
      | r1_xboole_0(A_130,B_131) ) ),
    inference(resolution,[status(thm)],[c_30,c_556])).

tff(c_570,plain,(
    ! [B_31,A_30] :
      ( k3_xboole_0(B_31,B_31) != k1_xboole_0
      | r1_xboole_0(A_30,B_31) ) ),
    inference(resolution,[status(thm)],[c_30,c_567])).

tff(c_578,plain,(
    ! [B_133,A_134] :
      ( k1_xboole_0 != B_133
      | r1_xboole_0(A_134,B_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_570])).

tff(c_28,plain,(
    ! [A_30,B_31,C_34] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_34,B_31)
      | ~ r2_hidden(C_34,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_620,plain,(
    ! [C_139,B_140,A_141] :
      ( ~ r2_hidden(C_139,B_140)
      | ~ r2_hidden(C_139,A_141)
      | k1_xboole_0 != B_140 ) ),
    inference(resolution,[status(thm)],[c_578,c_28])).

tff(c_827,plain,(
    ! [A_182,B_183,C_184,A_185] :
      ( ~ r2_hidden('#skF_5'(A_182,B_183,C_184),A_185)
      | k1_xboole_0 != B_183
      | ~ r2_hidden(A_182,k10_relat_1(C_184,B_183))
      | ~ v1_relat_1(C_184) ) ),
    inference(resolution,[status(thm)],[c_22,c_620])).

tff(c_837,plain,(
    ! [B_186,A_187,C_188] :
      ( k1_xboole_0 != B_186
      | ~ r2_hidden(A_187,k10_relat_1(C_188,B_186))
      | ~ v1_relat_1(C_188) ) ),
    inference(resolution,[status(thm)],[c_26,c_827])).

tff(c_910,plain,(
    ! [B_194,C_195,B_196] :
      ( k1_xboole_0 != B_194
      | ~ v1_relat_1(C_195)
      | r1_xboole_0(k10_relat_1(C_195,B_194),B_196) ) ),
    inference(resolution,[status(thm)],[c_32,c_837])).

tff(c_971,plain,(
    ! [C_200,B_201,B_202] :
      ( k3_xboole_0(k10_relat_1(C_200,B_201),B_202) = k1_xboole_0
      | k1_xboole_0 != B_201
      | ~ v1_relat_1(C_200) ) ),
    inference(resolution,[status(thm)],[c_910,c_14])).

tff(c_1039,plain,(
    ! [C_207,B_208] :
      ( k10_relat_1(C_207,B_208) = k1_xboole_0
      | k1_xboole_0 != B_208
      | ~ v1_relat_1(C_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_971,c_18])).

tff(c_1044,plain,(
    ! [B_209] :
      ( k10_relat_1('#skF_8',B_209) = k1_xboole_0
      | k1_xboole_0 != B_209 ) ),
    inference(resolution,[status(thm)],[c_34,c_1039])).

tff(c_834,plain,(
    ! [B_25,A_24,C_26] :
      ( k1_xboole_0 != B_25
      | ~ r2_hidden(A_24,k10_relat_1(C_26,B_25))
      | ~ v1_relat_1(C_26) ) ),
    inference(resolution,[status(thm)],[c_26,c_827])).

tff(c_1062,plain,(
    ! [B_209,A_24] :
      ( k1_xboole_0 != B_209
      | ~ r2_hidden(A_24,k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | k1_xboole_0 != B_209 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_834])).

tff(c_1082,plain,(
    ! [A_24,B_209] :
      ( ~ r2_hidden(A_24,k1_xboole_0)
      | k1_xboole_0 != B_209 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1062])).

tff(c_1084,plain,(
    ! [B_209] : k1_xboole_0 != B_209 ),
    inference(splitLeft,[status(thm)],[c_1082])).

tff(c_539,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1084,c_539])).

tff(c_1094,plain,(
    ! [A_24] : ~ r2_hidden(A_24,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1082])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1013,plain,(
    ! [A_203,C_204,B_205,D_206] :
      ( r2_hidden(A_203,k10_relat_1(C_204,B_205))
      | ~ r2_hidden(D_206,B_205)
      | ~ r2_hidden(k4_tarski(A_203,D_206),C_204)
      | ~ r2_hidden(D_206,k2_relat_1(C_204))
      | ~ v1_relat_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1619,plain,(
    ! [A_234,C_235,A_236,B_237] :
      ( r2_hidden(A_234,k10_relat_1(C_235,A_236))
      | ~ r2_hidden(k4_tarski(A_234,'#skF_6'(A_236,B_237)),C_235)
      | ~ r2_hidden('#skF_6'(A_236,B_237),k2_relat_1(C_235))
      | ~ v1_relat_1(C_235)
      | r1_xboole_0(A_236,B_237) ) ),
    inference(resolution,[status(thm)],[c_32,c_1013])).

tff(c_21895,plain,(
    ! [A_4460,A_4461,B_4462] :
      ( r2_hidden('#skF_4'(A_4460,k2_relat_1(A_4460),'#skF_6'(A_4461,B_4462)),k10_relat_1(A_4460,A_4461))
      | ~ v1_relat_1(A_4460)
      | r1_xboole_0(A_4461,B_4462)
      | ~ r2_hidden('#skF_6'(A_4461,B_4462),k2_relat_1(A_4460)) ) ),
    inference(resolution,[status(thm)],[c_2,c_1619])).

tff(c_22079,plain,(
    ! [B_4462] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),'#skF_6'('#skF_7',B_4462)),k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | r1_xboole_0('#skF_7',B_4462)
      | ~ r2_hidden('#skF_6'('#skF_7',B_4462),k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_21895])).

tff(c_22102,plain,(
    ! [B_4462] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),'#skF_6'('#skF_7',B_4462)),k1_xboole_0)
      | r1_xboole_0('#skF_7',B_4462)
      | ~ r2_hidden('#skF_6'('#skF_7',B_4462),k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_22079])).

tff(c_22104,plain,(
    ! [B_4484] :
      ( r1_xboole_0('#skF_7',B_4484)
      | ~ r2_hidden('#skF_6'('#skF_7',B_4484),k2_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_22102])).

tff(c_22115,plain,(
    r1_xboole_0('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_30,c_22104])).

tff(c_22120,plain,(
    k3_xboole_0('#skF_7',k2_relat_1('#skF_8')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22115,c_14])).

tff(c_22141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_749,c_22120])).

%------------------------------------------------------------------------------
