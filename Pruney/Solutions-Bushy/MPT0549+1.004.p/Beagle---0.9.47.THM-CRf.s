%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0549+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:28 EST 2020

% Result     : Theorem 10.00s
% Output     : CNFRefutation 10.00s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 266 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  133 ( 668 expanded)
%              Number of equality atoms :   33 ( 151 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_69,axiom,(
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

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_38,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7')
    | k9_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_77,plain,(
    k9_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_6'(A_31,B_32),B_32)
      | r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    ! [A_24,B_25,C_26] :
      ( r2_hidden('#skF_5'(A_24,B_25,C_26),B_25)
      | ~ r2_hidden(A_24,k9_relat_1(C_26,B_25))
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_402,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden('#skF_5'(A_103,B_104,C_105),k1_relat_1(C_105))
      | ~ r2_hidden(A_103,k9_relat_1(C_105,B_104))
      | ~ v1_relat_1(C_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,
    ( k9_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_79,plain,(
    r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_44])).

tff(c_90,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,B_50)
      | ~ r2_hidden(C_51,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_95,plain,(
    ! [C_51] :
      ( ~ r2_hidden(C_51,'#skF_7')
      | ~ r2_hidden(C_51,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_79,c_90])).

tff(c_414,plain,(
    ! [A_103,B_104] :
      ( ~ r2_hidden('#skF_5'(A_103,B_104,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_103,k9_relat_1('#skF_8',B_104))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_402,c_95])).

tff(c_423,plain,(
    ! [A_107,B_108] :
      ( ~ r2_hidden('#skF_5'(A_107,B_108,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_107,k9_relat_1('#skF_8',B_108)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_414])).

tff(c_427,plain,(
    ! [A_24] :
      ( ~ r2_hidden(A_24,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_22,c_423])).

tff(c_431,plain,(
    ! [A_109] : ~ r2_hidden(A_109,k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_427])).

tff(c_457,plain,(
    ! [A_110] : r1_xboole_0(A_110,k9_relat_1('#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_32,c_431])).

tff(c_14,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_505,plain,(
    ! [A_116] : k3_xboole_0(A_116,k9_relat_1('#skF_8','#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_457,c_14])).

tff(c_18,plain,(
    ! [A_22] : k3_xboole_0(A_22,A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_519,plain,(
    k9_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_18])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_519])).

tff(c_538,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_6'(A_31,B_32),A_31)
      | r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [C_16,A_1] :
      ( r2_hidden(k4_tarski(C_16,'#skF_4'(A_1,k1_relat_1(A_1),C_16)),A_1)
      | ~ r2_hidden(C_16,k1_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_715,plain,(
    ! [C_154,A_155] :
      ( r2_hidden(k4_tarski(C_154,'#skF_4'(A_155,k1_relat_1(A_155),C_154)),A_155)
      | ~ r2_hidden(C_154,k1_relat_1(A_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,B_21)
      | k3_xboole_0(A_20,B_21) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_553,plain,(
    ! [A_124,B_125,C_126] :
      ( ~ r1_xboole_0(A_124,B_125)
      | ~ r2_hidden(C_126,B_125)
      | ~ r2_hidden(C_126,A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_558,plain,(
    ! [C_129,B_130,A_131] :
      ( ~ r2_hidden(C_129,B_130)
      | ~ r2_hidden(C_129,A_131)
      | k3_xboole_0(A_131,B_130) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_553])).

tff(c_568,plain,(
    ! [A_132,B_133,A_134] :
      ( ~ r2_hidden('#skF_6'(A_132,B_133),A_134)
      | k3_xboole_0(A_134,A_132) != k1_xboole_0
      | r1_xboole_0(A_132,B_133) ) ),
    inference(resolution,[status(thm)],[c_34,c_558])).

tff(c_571,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,A_31) != k1_xboole_0
      | r1_xboole_0(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_34,c_568])).

tff(c_579,plain,(
    ! [A_135,B_136] :
      ( k1_xboole_0 != A_135
      | r1_xboole_0(A_135,B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_571])).

tff(c_30,plain,(
    ! [A_31,B_32,C_35] :
      ( ~ r1_xboole_0(A_31,B_32)
      | ~ r2_hidden(C_35,B_32)
      | ~ r2_hidden(C_35,A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_588,plain,(
    ! [C_35,B_136,A_135] :
      ( ~ r2_hidden(C_35,B_136)
      | ~ r2_hidden(C_35,A_135)
      | k1_xboole_0 != A_135 ) ),
    inference(resolution,[status(thm)],[c_579,c_30])).

tff(c_831,plain,(
    ! [C_182,A_183,A_184] :
      ( ~ r2_hidden(k4_tarski(C_182,'#skF_4'(A_183,k1_relat_1(A_183),C_182)),A_184)
      | k1_xboole_0 != A_184
      | ~ r2_hidden(C_182,k1_relat_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_715,c_588])).

tff(c_837,plain,(
    ! [A_185,C_186] :
      ( k1_xboole_0 != A_185
      | ~ r2_hidden(C_186,k1_relat_1(A_185)) ) ),
    inference(resolution,[status(thm)],[c_2,c_831])).

tff(c_886,plain,(
    ! [A_189,A_190] :
      ( k1_xboole_0 != A_189
      | r1_xboole_0(A_190,k1_relat_1(A_189)) ) ),
    inference(resolution,[status(thm)],[c_32,c_837])).

tff(c_959,plain,(
    ! [A_195,A_196] :
      ( k3_xboole_0(A_195,k1_relat_1(A_196)) = k1_xboole_0
      | k1_xboole_0 != A_196 ) ),
    inference(resolution,[status(thm)],[c_886,c_14])).

tff(c_1000,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_18])).

tff(c_1001,plain,(
    ! [A_197] :
      ( k1_relat_1(A_197) = k1_xboole_0
      | k1_xboole_0 != A_197 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_18])).

tff(c_867,plain,(
    ! [A_185,C_16] :
      ( k1_xboole_0 != A_185
      | ~ r2_hidden(C_16,k1_relat_1(k1_relat_1(A_185))) ) ),
    inference(resolution,[status(thm)],[c_2,c_837])).

tff(c_1010,plain,(
    ! [A_197,C_16] :
      ( k1_xboole_0 != A_197
      | ~ r2_hidden(C_16,k1_relat_1(k1_xboole_0))
      | k1_xboole_0 != A_197 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_867])).

tff(c_1049,plain,(
    ! [A_197,C_16] :
      ( k1_xboole_0 != A_197
      | ~ r2_hidden(C_16,k1_xboole_0)
      | k1_xboole_0 != A_197 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1010])).

tff(c_1178,plain,(
    ! [A_197] :
      ( k1_xboole_0 != A_197
      | k1_xboole_0 != A_197 ) ),
    inference(splitLeft,[status(thm)],[c_1049])).

tff(c_1184,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1178])).

tff(c_1185,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1049])).

tff(c_539,plain,(
    k9_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1060,plain,(
    ! [A_198,C_199,B_200,D_201] :
      ( r2_hidden(A_198,k9_relat_1(C_199,B_200))
      | ~ r2_hidden(D_201,B_200)
      | ~ r2_hidden(k4_tarski(D_201,A_198),C_199)
      | ~ r2_hidden(D_201,k1_relat_1(C_199))
      | ~ v1_relat_1(C_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2331,plain,(
    ! [A_247,C_248,B_249,A_250] :
      ( r2_hidden(A_247,k9_relat_1(C_248,B_249))
      | ~ r2_hidden(k4_tarski('#skF_6'(A_250,B_249),A_247),C_248)
      | ~ r2_hidden('#skF_6'(A_250,B_249),k1_relat_1(C_248))
      | ~ v1_relat_1(C_248)
      | r1_xboole_0(A_250,B_249) ) ),
    inference(resolution,[status(thm)],[c_32,c_1060])).

tff(c_31792,plain,(
    ! [A_646,A_647,B_648] :
      ( r2_hidden('#skF_4'(A_646,k1_relat_1(A_646),'#skF_6'(A_647,B_648)),k9_relat_1(A_646,B_648))
      | ~ v1_relat_1(A_646)
      | r1_xboole_0(A_647,B_648)
      | ~ r2_hidden('#skF_6'(A_647,B_648),k1_relat_1(A_646)) ) ),
    inference(resolution,[status(thm)],[c_2,c_2331])).

tff(c_31958,plain,(
    ! [A_647] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'(A_647,'#skF_7')),k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | r1_xboole_0(A_647,'#skF_7')
      | ~ r2_hidden('#skF_6'(A_647,'#skF_7'),k1_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_31792])).

tff(c_31987,plain,(
    ! [A_647] :
      ( r2_hidden('#skF_4'('#skF_8',k1_relat_1('#skF_8'),'#skF_6'(A_647,'#skF_7')),k1_xboole_0)
      | r1_xboole_0(A_647,'#skF_7')
      | ~ r2_hidden('#skF_6'(A_647,'#skF_7'),k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_31958])).

tff(c_31989,plain,(
    ! [A_649] :
      ( r1_xboole_0(A_649,'#skF_7')
      | ~ r2_hidden('#skF_6'(A_649,'#skF_7'),k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1185,c_31987])).

tff(c_32002,plain,(
    r1_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_31989])).

tff(c_32006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_538,c_538,c_32002])).

%------------------------------------------------------------------------------
