%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0469+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:21 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   61 (  89 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 128 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_54,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_56,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_44,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_49,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_237,plain,(
    ! [C_90,A_91] :
      ( r2_hidden(k4_tarski(C_90,'#skF_5'(A_91,k1_relat_1(A_91),C_90)),A_91)
      | ~ r2_hidden(C_90,k1_relat_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_148,plain,(
    ! [A_82,C_83] :
      ( r2_hidden(k4_tarski('#skF_9'(A_82,k2_relat_1(A_82),C_83),C_83),A_82)
      | ~ r2_hidden(C_83,k2_relat_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [B_48,A_47] :
      ( ~ v1_xboole_0(B_48)
      | ~ r2_hidden(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_164,plain,(
    ! [A_84,C_85] :
      ( ~ v1_xboole_0(A_84)
      | ~ r2_hidden(C_85,k2_relat_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_148,c_42])).

tff(c_180,plain,(
    ! [A_86,B_87] :
      ( ~ v1_xboole_0(A_86)
      | r1_tarski(k2_relat_1(A_86),B_87) ) ),
    inference(resolution,[status(thm)],[c_12,c_164])).

tff(c_40,plain,(
    ! [A_46] : r1_tarski(k1_xboole_0,A_46) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_59,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_50])).

tff(c_196,plain,(
    ! [A_88] :
      ( k2_relat_1(A_88) = k1_xboole_0
      | ~ v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_180,c_59])).

tff(c_200,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_196])).

tff(c_163,plain,(
    ! [A_82,C_83] :
      ( ~ v1_xboole_0(A_82)
      | ~ r2_hidden(C_83,k2_relat_1(A_82)) ) ),
    inference(resolution,[status(thm)],[c_148,c_42])).

tff(c_207,plain,(
    ! [C_83] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_163])).

tff(c_216,plain,(
    ! [C_83] : ~ r2_hidden(C_83,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_207])).

tff(c_263,plain,(
    ! [C_92] : ~ r2_hidden(C_92,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_237,c_216])).

tff(c_284,plain,(
    ! [B_93] : r1_tarski(k1_relat_1(k1_xboole_0),B_93) ),
    inference(resolution,[status(thm)],[c_12,c_263])).

tff(c_293,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_284,c_59])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_293])).

tff(c_303,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_26,plain,(
    ! [A_27,C_42] :
      ( r2_hidden(k4_tarski('#skF_9'(A_27,k2_relat_1(A_27),C_42),C_42),A_27)
      | ~ r2_hidden(C_42,k2_relat_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_304,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_407,plain,(
    ! [C_123,A_124] :
      ( r2_hidden(k4_tarski(C_123,'#skF_5'(A_124,k1_relat_1(A_124),C_123)),A_124)
      | ~ r2_hidden(C_123,k1_relat_1(A_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_427,plain,(
    ! [A_125,C_126] :
      ( ~ v1_xboole_0(A_125)
      | ~ r2_hidden(C_126,k1_relat_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_407,c_42])).

tff(c_442,plain,(
    ! [C_126] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_126,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_427])).

tff(c_469,plain,(
    ! [C_129] : ~ r2_hidden(C_129,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_442])).

tff(c_492,plain,(
    ! [C_130] : ~ r2_hidden(C_130,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_26,c_469])).

tff(c_513,plain,(
    ! [B_131] : r1_tarski(k2_relat_1(k1_xboole_0),B_131) ),
    inference(resolution,[status(thm)],[c_12,c_492])).

tff(c_309,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_318,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_40,c_309])).

tff(c_522,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_513,c_318])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_522])).

%------------------------------------------------------------------------------
