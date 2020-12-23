%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:04 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 152 expanded)
%              Number of leaves         :   41 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 174 expanded)
%              Number of equality atoms :   63 ( 107 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
      <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_86,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_130,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_66,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_270,plain,(
    ! [A_85,B_86] : k1_enumset1(A_85,A_85,B_86) = k2_tarski(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44,plain,(
    ! [E_30,A_24,B_25] : r2_hidden(E_30,k1_enumset1(A_24,B_25,E_30)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_288,plain,(
    ! [B_87,A_88] : r2_hidden(B_87,k2_tarski(A_88,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_44])).

tff(c_291,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_288])).

tff(c_46,plain,(
    ! [E_30,A_24,C_26] : r2_hidden(E_30,k1_enumset1(A_24,E_30,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_279,plain,(
    ! [A_85,B_86] : r2_hidden(A_85,k2_tarski(A_85,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_46])).

tff(c_36,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_233,plain,(
    ! [A_79,B_80] :
      ( k2_xboole_0(A_79,B_80) = B_80
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_237,plain,(
    ! [B_10] : k2_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_233])).

tff(c_137,plain,(
    ! [B_76,A_77] : k5_xboole_0(B_76,A_77) = k5_xboole_0(A_77,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_153,plain,(
    ! [A_77] : k5_xboole_0(k1_xboole_0,A_77) = A_77 ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_32])).

tff(c_522,plain,(
    ! [A_119,B_120] : k5_xboole_0(k5_xboole_0(A_119,B_120),k2_xboole_0(A_119,B_120)) = k3_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_579,plain,(
    ! [A_19] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_19,A_19)) = k3_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_522])).

tff(c_586,plain,(
    ! [A_121] : k3_xboole_0(A_121,A_121) = A_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_153,c_579])).

tff(c_28,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_600,plain,(
    ! [A_121] : k5_xboole_0(A_121,A_121) = k4_xboole_0(A_121,A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_28])).

tff(c_610,plain,(
    ! [A_122] : k4_xboole_0(A_122,A_122) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_600])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_647,plain,(
    ! [D_123,A_124] :
      ( ~ r2_hidden(D_123,A_124)
      | ~ r2_hidden(D_123,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_6])).

tff(c_663,plain,(
    ! [A_85] : ~ r2_hidden(A_85,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_279,c_647])).

tff(c_90,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_132,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_1253,plain,(
    ! [D_143,A_144,B_145] :
      ( r2_hidden(D_143,k4_xboole_0(A_144,B_145))
      | r2_hidden(D_143,B_145)
      | ~ r2_hidden(D_143,A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1271,plain,(
    ! [D_143] :
      ( r2_hidden(D_143,k1_xboole_0)
      | r2_hidden(D_143,'#skF_8')
      | ~ r2_hidden(D_143,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_1253])).

tff(c_1278,plain,(
    ! [D_146] :
      ( r2_hidden(D_146,'#skF_8')
      | ~ r2_hidden(D_146,k1_tarski('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_663,c_1271])).

tff(c_1282,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_291,c_1278])).

tff(c_1286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1282])).

tff(c_1287,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_80,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(k1_tarski(A_59),B_60) = B_60
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1933,plain,(
    ! [A_196,B_197] : k5_xboole_0(k5_xboole_0(A_196,B_197),k2_xboole_0(A_196,B_197)) = k3_xboole_0(A_196,B_197) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_16,B_17,C_18] : k5_xboole_0(k5_xboole_0(A_16,B_17),C_18) = k5_xboole_0(A_16,k5_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5820,plain,(
    ! [A_345,B_346] : k5_xboole_0(A_345,k5_xboole_0(B_346,k2_xboole_0(A_345,B_346))) = k3_xboole_0(A_345,B_346) ),
    inference(superposition,[status(thm),theory(equality)],[c_1933,c_34])).

tff(c_1289,plain,(
    ! [B_147,A_148] : k5_xboole_0(B_147,A_148) = k5_xboole_0(A_148,B_147) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1305,plain,(
    ! [A_148] : k5_xboole_0(k1_xboole_0,A_148) = A_148 ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_32])).

tff(c_1676,plain,(
    ! [A_189,B_190,C_191] : k5_xboole_0(k5_xboole_0(A_189,B_190),C_191) = k5_xboole_0(A_189,k5_xboole_0(B_190,C_191)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1762,plain,(
    ! [A_19,C_191] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_191)) = k5_xboole_0(k1_xboole_0,C_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1676])).

tff(c_1775,plain,(
    ! [A_19,C_191] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_191)) = C_191 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1305,c_1762])).

tff(c_5870,plain,(
    ! [B_346,A_345] : k5_xboole_0(B_346,k2_xboole_0(A_345,B_346)) = k5_xboole_0(A_345,k3_xboole_0(A_345,B_346)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5820,c_1775])).

tff(c_5967,plain,(
    ! [B_347,A_348] : k5_xboole_0(B_347,k2_xboole_0(A_348,B_347)) = k4_xboole_0(A_348,B_347) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5870])).

tff(c_6049,plain,(
    ! [B_60,A_59] :
      ( k5_xboole_0(B_60,B_60) = k4_xboole_0(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_5967])).

tff(c_6288,plain,(
    ! [A_353,B_354] :
      ( k4_xboole_0(k1_tarski(A_353),B_354) = k1_xboole_0
      | ~ r2_hidden(A_353,B_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6049])).

tff(c_1288,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_88,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1430,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1288,c_88])).

tff(c_6341,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6288,c_1430])).

tff(c_6374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_6341])).

tff(c_6375,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_38,plain,(
    ! [A_20,B_21] : k5_xboole_0(k5_xboole_0(A_20,B_21),k2_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6847,plain,(
    ! [A_408,B_409,C_410] : k5_xboole_0(k5_xboole_0(A_408,B_409),C_410) = k5_xboole_0(A_408,k5_xboole_0(B_409,C_410)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12329,plain,(
    ! [A_575,B_576] : k5_xboole_0(A_575,k5_xboole_0(B_576,k2_xboole_0(A_575,B_576))) = k3_xboole_0(A_575,B_576) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6847])).

tff(c_6378,plain,(
    ! [B_358,A_359] : k5_xboole_0(B_358,A_359) = k5_xboole_0(A_359,B_358) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6394,plain,(
    ! [A_359] : k5_xboole_0(k1_xboole_0,A_359) = A_359 ),
    inference(superposition,[status(thm),theory(equality)],[c_6378,c_32])).

tff(c_6935,plain,(
    ! [A_19,C_410] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_410)) = k5_xboole_0(k1_xboole_0,C_410) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6847])).

tff(c_6948,plain,(
    ! [A_19,C_410] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_410)) = C_410 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6394,c_6935])).

tff(c_12382,plain,(
    ! [B_576,A_575] : k5_xboole_0(B_576,k2_xboole_0(A_575,B_576)) = k5_xboole_0(A_575,k3_xboole_0(A_575,B_576)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12329,c_6948])).

tff(c_12483,plain,(
    ! [B_577,A_578] : k5_xboole_0(B_577,k2_xboole_0(A_578,B_577)) = k4_xboole_0(A_578,B_577) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12382])).

tff(c_12571,plain,(
    ! [B_60,A_59] :
      ( k5_xboole_0(B_60,B_60) = k4_xboole_0(k1_tarski(A_59),B_60)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_12483])).

tff(c_12826,plain,(
    ! [A_583,B_584] :
      ( k4_xboole_0(k1_tarski(A_583),B_584) = k1_xboole_0
      | ~ r2_hidden(A_583,B_584) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_12571])).

tff(c_6376,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_84,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6487,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6376,c_84])).

tff(c_12888,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_12826,c_6487])).

tff(c_12921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6375,c_12888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:47:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.60/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.72  
% 7.60/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.72  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 7.60/2.72  
% 7.60/2.72  %Foreground sorts:
% 7.60/2.72  
% 7.60/2.72  
% 7.60/2.72  %Background operators:
% 7.60/2.72  
% 7.60/2.72  
% 7.60/2.72  %Foreground operators:
% 7.60/2.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.60/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.60/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.60/2.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.60/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.60/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.60/2.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.60/2.72  tff('#skF_7', type, '#skF_7': $i).
% 7.60/2.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.60/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.60/2.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.60/2.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.60/2.72  tff('#skF_5', type, '#skF_5': $i).
% 7.60/2.72  tff('#skF_6', type, '#skF_6': $i).
% 7.60/2.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.60/2.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.60/2.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.60/2.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.60/2.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.60/2.72  tff('#skF_8', type, '#skF_8': $i).
% 7.60/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.60/2.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.60/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.60/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.60/2.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.60/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.60/2.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.60/2.72  
% 7.60/2.73  tff(f_99, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 7.60/2.73  tff(f_76, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.60/2.73  tff(f_78, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.60/2.73  tff(f_74, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 7.60/2.73  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 7.60/2.73  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.60/2.73  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.60/2.73  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 7.60/2.73  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 7.60/2.73  tff(f_57, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 7.60/2.73  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.60/2.73  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.60/2.73  tff(f_92, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 7.60/2.73  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 7.60/2.73  tff(c_86, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.60/2.73  tff(c_130, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_86])).
% 7.60/2.73  tff(c_66, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.60/2.73  tff(c_270, plain, (![A_85, B_86]: (k1_enumset1(A_85, A_85, B_86)=k2_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.60/2.73  tff(c_44, plain, (![E_30, A_24, B_25]: (r2_hidden(E_30, k1_enumset1(A_24, B_25, E_30)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.60/2.73  tff(c_288, plain, (![B_87, A_88]: (r2_hidden(B_87, k2_tarski(A_88, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_44])).
% 7.60/2.73  tff(c_291, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_288])).
% 7.60/2.73  tff(c_46, plain, (![E_30, A_24, C_26]: (r2_hidden(E_30, k1_enumset1(A_24, E_30, C_26)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.60/2.73  tff(c_279, plain, (![A_85, B_86]: (r2_hidden(A_85, k2_tarski(A_85, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_270, c_46])).
% 7.60/2.73  tff(c_36, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.60/2.73  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.60/2.73  tff(c_233, plain, (![A_79, B_80]: (k2_xboole_0(A_79, B_80)=B_80 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.60/2.73  tff(c_237, plain, (![B_10]: (k2_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_233])).
% 7.60/2.73  tff(c_137, plain, (![B_76, A_77]: (k5_xboole_0(B_76, A_77)=k5_xboole_0(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.60/2.73  tff(c_32, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.60/2.73  tff(c_153, plain, (![A_77]: (k5_xboole_0(k1_xboole_0, A_77)=A_77)), inference(superposition, [status(thm), theory('equality')], [c_137, c_32])).
% 7.60/2.73  tff(c_522, plain, (![A_119, B_120]: (k5_xboole_0(k5_xboole_0(A_119, B_120), k2_xboole_0(A_119, B_120))=k3_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.60/2.73  tff(c_579, plain, (![A_19]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_19, A_19))=k3_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_36, c_522])).
% 7.60/2.73  tff(c_586, plain, (![A_121]: (k3_xboole_0(A_121, A_121)=A_121)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_153, c_579])).
% 7.60/2.73  tff(c_28, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.60/2.73  tff(c_600, plain, (![A_121]: (k5_xboole_0(A_121, A_121)=k4_xboole_0(A_121, A_121))), inference(superposition, [status(thm), theory('equality')], [c_586, c_28])).
% 7.60/2.73  tff(c_610, plain, (![A_122]: (k4_xboole_0(A_122, A_122)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_600])).
% 7.60/2.73  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.60/2.73  tff(c_647, plain, (![D_123, A_124]: (~r2_hidden(D_123, A_124) | ~r2_hidden(D_123, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_610, c_6])).
% 7.60/2.73  tff(c_663, plain, (![A_85]: (~r2_hidden(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_279, c_647])).
% 7.60/2.73  tff(c_90, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.60/2.73  tff(c_132, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_90])).
% 7.60/2.73  tff(c_1253, plain, (![D_143, A_144, B_145]: (r2_hidden(D_143, k4_xboole_0(A_144, B_145)) | r2_hidden(D_143, B_145) | ~r2_hidden(D_143, A_144))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.60/2.73  tff(c_1271, plain, (![D_143]: (r2_hidden(D_143, k1_xboole_0) | r2_hidden(D_143, '#skF_8') | ~r2_hidden(D_143, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_132, c_1253])).
% 7.60/2.73  tff(c_1278, plain, (![D_146]: (r2_hidden(D_146, '#skF_8') | ~r2_hidden(D_146, k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_663, c_1271])).
% 7.60/2.73  tff(c_1282, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_291, c_1278])).
% 7.60/2.73  tff(c_1286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_1282])).
% 7.60/2.73  tff(c_1287, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_90])).
% 7.60/2.73  tff(c_80, plain, (![A_59, B_60]: (k2_xboole_0(k1_tarski(A_59), B_60)=B_60 | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.60/2.73  tff(c_1933, plain, (![A_196, B_197]: (k5_xboole_0(k5_xboole_0(A_196, B_197), k2_xboole_0(A_196, B_197))=k3_xboole_0(A_196, B_197))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.60/2.73  tff(c_34, plain, (![A_16, B_17, C_18]: (k5_xboole_0(k5_xboole_0(A_16, B_17), C_18)=k5_xboole_0(A_16, k5_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.60/2.73  tff(c_5820, plain, (![A_345, B_346]: (k5_xboole_0(A_345, k5_xboole_0(B_346, k2_xboole_0(A_345, B_346)))=k3_xboole_0(A_345, B_346))), inference(superposition, [status(thm), theory('equality')], [c_1933, c_34])).
% 7.60/2.73  tff(c_1289, plain, (![B_147, A_148]: (k5_xboole_0(B_147, A_148)=k5_xboole_0(A_148, B_147))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.60/2.73  tff(c_1305, plain, (![A_148]: (k5_xboole_0(k1_xboole_0, A_148)=A_148)), inference(superposition, [status(thm), theory('equality')], [c_1289, c_32])).
% 7.60/2.73  tff(c_1676, plain, (![A_189, B_190, C_191]: (k5_xboole_0(k5_xboole_0(A_189, B_190), C_191)=k5_xboole_0(A_189, k5_xboole_0(B_190, C_191)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.60/2.73  tff(c_1762, plain, (![A_19, C_191]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_191))=k5_xboole_0(k1_xboole_0, C_191))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1676])).
% 7.60/2.73  tff(c_1775, plain, (![A_19, C_191]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_191))=C_191)), inference(demodulation, [status(thm), theory('equality')], [c_1305, c_1762])).
% 7.60/2.73  tff(c_5870, plain, (![B_346, A_345]: (k5_xboole_0(B_346, k2_xboole_0(A_345, B_346))=k5_xboole_0(A_345, k3_xboole_0(A_345, B_346)))), inference(superposition, [status(thm), theory('equality')], [c_5820, c_1775])).
% 7.60/2.73  tff(c_5967, plain, (![B_347, A_348]: (k5_xboole_0(B_347, k2_xboole_0(A_348, B_347))=k4_xboole_0(A_348, B_347))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5870])).
% 7.60/2.73  tff(c_6049, plain, (![B_60, A_59]: (k5_xboole_0(B_60, B_60)=k4_xboole_0(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_80, c_5967])).
% 7.60/2.73  tff(c_6288, plain, (![A_353, B_354]: (k4_xboole_0(k1_tarski(A_353), B_354)=k1_xboole_0 | ~r2_hidden(A_353, B_354))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6049])).
% 7.60/2.73  tff(c_1288, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_90])).
% 7.60/2.73  tff(c_88, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.60/2.73  tff(c_1430, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1288, c_88])).
% 7.60/2.73  tff(c_6341, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6288, c_1430])).
% 7.60/2.73  tff(c_6374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1287, c_6341])).
% 7.60/2.73  tff(c_6375, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 7.60/2.73  tff(c_38, plain, (![A_20, B_21]: (k5_xboole_0(k5_xboole_0(A_20, B_21), k2_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.60/2.73  tff(c_6847, plain, (![A_408, B_409, C_410]: (k5_xboole_0(k5_xboole_0(A_408, B_409), C_410)=k5_xboole_0(A_408, k5_xboole_0(B_409, C_410)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.60/2.73  tff(c_12329, plain, (![A_575, B_576]: (k5_xboole_0(A_575, k5_xboole_0(B_576, k2_xboole_0(A_575, B_576)))=k3_xboole_0(A_575, B_576))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6847])).
% 7.60/2.73  tff(c_6378, plain, (![B_358, A_359]: (k5_xboole_0(B_358, A_359)=k5_xboole_0(A_359, B_358))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.60/2.73  tff(c_6394, plain, (![A_359]: (k5_xboole_0(k1_xboole_0, A_359)=A_359)), inference(superposition, [status(thm), theory('equality')], [c_6378, c_32])).
% 7.60/2.73  tff(c_6935, plain, (![A_19, C_410]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_410))=k5_xboole_0(k1_xboole_0, C_410))), inference(superposition, [status(thm), theory('equality')], [c_36, c_6847])).
% 7.60/2.73  tff(c_6948, plain, (![A_19, C_410]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_410))=C_410)), inference(demodulation, [status(thm), theory('equality')], [c_6394, c_6935])).
% 7.60/2.73  tff(c_12382, plain, (![B_576, A_575]: (k5_xboole_0(B_576, k2_xboole_0(A_575, B_576))=k5_xboole_0(A_575, k3_xboole_0(A_575, B_576)))), inference(superposition, [status(thm), theory('equality')], [c_12329, c_6948])).
% 7.60/2.73  tff(c_12483, plain, (![B_577, A_578]: (k5_xboole_0(B_577, k2_xboole_0(A_578, B_577))=k4_xboole_0(A_578, B_577))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12382])).
% 7.60/2.73  tff(c_12571, plain, (![B_60, A_59]: (k5_xboole_0(B_60, B_60)=k4_xboole_0(k1_tarski(A_59), B_60) | ~r2_hidden(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_80, c_12483])).
% 7.60/2.73  tff(c_12826, plain, (![A_583, B_584]: (k4_xboole_0(k1_tarski(A_583), B_584)=k1_xboole_0 | ~r2_hidden(A_583, B_584))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_12571])).
% 7.60/2.73  tff(c_6376, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 7.60/2.73  tff(c_84, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0 | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.60/2.73  tff(c_6487, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6376, c_84])).
% 7.60/2.73  tff(c_12888, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_12826, c_6487])).
% 7.60/2.73  tff(c_12921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6375, c_12888])).
% 7.60/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/2.73  
% 7.60/2.73  Inference rules
% 7.60/2.73  ----------------------
% 7.60/2.73  #Ref     : 0
% 7.60/2.73  #Sup     : 3175
% 7.60/2.73  #Fact    : 0
% 7.60/2.73  #Define  : 0
% 7.60/2.73  #Split   : 2
% 7.60/2.73  #Chain   : 0
% 7.60/2.73  #Close   : 0
% 7.60/2.73  
% 7.60/2.73  Ordering : KBO
% 7.60/2.73  
% 7.60/2.73  Simplification rules
% 7.60/2.73  ----------------------
% 7.60/2.73  #Subsume      : 206
% 7.60/2.73  #Demod        : 2798
% 7.60/2.73  #Tautology    : 1789
% 7.60/2.73  #SimpNegUnit  : 24
% 7.60/2.74  #BackRed      : 31
% 7.60/2.74  
% 7.60/2.74  #Partial instantiations: 0
% 7.60/2.74  #Strategies tried      : 1
% 7.60/2.74  
% 7.60/2.74  Timing (in seconds)
% 7.60/2.74  ----------------------
% 7.60/2.74  Preprocessing        : 0.35
% 7.60/2.74  Parsing              : 0.18
% 7.60/2.74  CNF conversion       : 0.03
% 7.60/2.74  Main loop            : 1.62
% 7.60/2.74  Inferencing          : 0.47
% 7.60/2.74  Reduction            : 0.77
% 7.60/2.74  Demodulation         : 0.65
% 7.60/2.74  BG Simplification    : 0.07
% 7.60/2.74  Subsumption          : 0.22
% 7.60/2.74  Abstraction          : 0.09
% 7.60/2.74  MUC search           : 0.00
% 7.60/2.74  Cooper               : 0.00
% 7.60/2.74  Total                : 2.00
% 7.60/2.74  Index Insertion      : 0.00
% 7.60/2.74  Index Deletion       : 0.00
% 7.60/2.74  Index Matching       : 0.00
% 7.60/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
