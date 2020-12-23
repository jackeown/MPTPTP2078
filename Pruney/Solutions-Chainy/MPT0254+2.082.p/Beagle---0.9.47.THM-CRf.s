%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:30 EST 2020

% Result     : Theorem 6.17s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 356 expanded)
%              Number of leaves         :   41 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 368 expanded)
%              Number of equality atoms :   61 ( 310 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_88,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_90,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_28,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_885,plain,(
    ! [A_141,B_142] : k5_xboole_0(k5_xboole_0(A_141,B_142),k3_xboole_0(A_141,B_142)) = k2_xboole_0(A_141,B_142) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_5167,plain,(
    ! [A_14844,B_14845] : k5_xboole_0(k5_xboole_0(A_14844,B_14845),k3_xboole_0(B_14845,A_14844)) = k2_xboole_0(A_14844,B_14845) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_885])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] : k5_xboole_0(k5_xboole_0(A_22,B_23),C_24) = k5_xboole_0(A_22,k5_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5198,plain,(
    ! [A_14844,B_14845] : k5_xboole_0(A_14844,k5_xboole_0(B_14845,k3_xboole_0(B_14845,A_14844))) = k2_xboole_0(A_14844,B_14845) ),
    inference(superposition,[status(thm),theory(equality)],[c_5167,c_30])).

tff(c_5351,plain,(
    ! [A_15011,B_15012] : k5_xboole_0(A_15011,k4_xboole_0(B_15012,A_15011)) = k2_xboole_0(A_15011,B_15012) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_5198])).

tff(c_155,plain,(
    ! [B_80,A_81] : k5_xboole_0(B_80,A_81) = k5_xboole_0(A_81,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_171,plain,(
    ! [A_81] : k5_xboole_0(k1_xboole_0,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_28])).

tff(c_32,plain,(
    ! [A_25] : k5_xboole_0(A_25,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_613,plain,(
    ! [A_127,B_128,C_129] : k5_xboole_0(k5_xboole_0(A_127,B_128),C_129) = k5_xboole_0(A_127,k5_xboole_0(B_128,C_129)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_670,plain,(
    ! [A_25,C_129] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_129)) = k5_xboole_0(k1_xboole_0,C_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_613])).

tff(c_688,plain,(
    ! [A_25,C_129] : k5_xboole_0(A_25,k5_xboole_0(A_25,C_129)) = C_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_670])).

tff(c_5534,plain,(
    ! [A_15345,B_15346] : k5_xboole_0(A_15345,k2_xboole_0(A_15345,B_15346)) = k4_xboole_0(B_15346,A_15345) ),
    inference(superposition,[status(thm),theory(equality)],[c_5351,c_688])).

tff(c_5601,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_5534])).

tff(c_5614,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5601])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_694,plain,(
    ! [A_133,C_134] : k5_xboole_0(A_133,k5_xboole_0(A_133,C_134)) = C_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_670])).

tff(c_737,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_694])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_317,plain,(
    ! [A_100,B_101] :
      ( k3_xboole_0(A_100,B_101) = A_100
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1315,plain,(
    ! [A_164,B_165] : k3_xboole_0(k4_xboole_0(A_164,B_165),A_164) = k4_xboole_0(A_164,B_165) ),
    inference(resolution,[status(thm)],[c_26,c_317])).

tff(c_34,plain,(
    ! [A_26,B_27] : k5_xboole_0(k5_xboole_0(A_26,B_27),k3_xboole_0(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1321,plain,(
    ! [A_164,B_165] : k5_xboole_0(k5_xboole_0(k4_xboole_0(A_164,B_165),A_164),k4_xboole_0(A_164,B_165)) = k2_xboole_0(k4_xboole_0(A_164,B_165),A_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_34])).

tff(c_1366,plain,(
    ! [A_164,B_165] : k2_xboole_0(k4_xboole_0(A_164,B_165),A_164) = A_164 ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_4,c_4,c_1321])).

tff(c_5660,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5614,c_1366])).

tff(c_5896,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5660,c_76])).

tff(c_60,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_254,plain,(
    ! [A_88,B_89] : k1_enumset1(A_88,A_88,B_89) = k2_tarski(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [E_34,A_28,C_30] : r2_hidden(E_34,k1_enumset1(A_28,E_34,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_272,plain,(
    ! [A_90,B_91] : r2_hidden(A_90,k2_tarski(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_40])).

tff(c_275,plain,(
    ! [A_35] : r2_hidden(A_35,k1_tarski(A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_272])).

tff(c_18,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_328,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_18,c_317])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_531,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_xboole_0(A_112,B_113)
      | ~ r2_hidden(C_114,k3_xboole_0(A_112,B_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_568,plain,(
    ! [B_117,C_118] :
      ( ~ r1_xboole_0(B_117,B_117)
      | ~ r2_hidden(C_118,B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_531])).

tff(c_571,plain,(
    ! [C_118,B_6] :
      ( ~ r2_hidden(C_118,B_6)
      | k3_xboole_0(B_6,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_568])).

tff(c_575,plain,(
    ! [C_119,B_120] :
      ( ~ r2_hidden(C_119,B_120)
      | k1_xboole_0 != B_120 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_571])).

tff(c_595,plain,(
    ! [A_35] : k1_tarski(A_35) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_275,c_575])).

tff(c_5922,plain,(
    ! [A_35] : k1_tarski(A_35) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_595])).

tff(c_5666,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5614,c_26])).

tff(c_1330,plain,(
    ! [A_164,B_165] : k5_xboole_0(k4_xboole_0(A_164,B_165),k4_xboole_0(A_164,B_165)) = k4_xboole_0(k4_xboole_0(A_164,B_165),A_164) ),
    inference(superposition,[status(thm),theory(equality)],[c_1315,c_20])).

tff(c_1367,plain,(
    ! [A_164,B_165] : k4_xboole_0(k4_xboole_0(A_164,B_165),A_164) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1330])).

tff(c_5657,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5614,c_1367])).

tff(c_6585,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5896,c_5657])).

tff(c_465,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_472,plain,(
    ! [A_19,B_20] :
      ( k4_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,k4_xboole_0(A_19,B_20)) ) ),
    inference(resolution,[status(thm)],[c_26,c_465])).

tff(c_6595,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6585,c_472])).

tff(c_6641,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5666,c_6585,c_6595])).

tff(c_6643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5922,c_6641])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.17/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.17/2.29  
% 6.17/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.47/2.29  
% 6.47/2.29  %Foreground sorts:
% 6.47/2.29  
% 6.47/2.29  
% 6.47/2.29  %Background operators:
% 6.47/2.29  
% 6.47/2.29  
% 6.47/2.29  %Foreground operators:
% 6.47/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.47/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.47/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.47/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.47/2.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.47/2.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.47/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.47/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.47/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.47/2.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.47/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.47/2.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.47/2.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.47/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.47/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.47/2.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.47/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.47/2.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.47/2.29  
% 6.47/2.31  tff(f_65, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.47/2.31  tff(f_106, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.47/2.31  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.47/2.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.47/2.31  tff(f_71, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.47/2.31  tff(f_67, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.47/2.31  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.47/2.31  tff(f_69, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.47/2.31  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.47/2.31  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.47/2.31  tff(f_88, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.47/2.31  tff(f_90, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.47/2.31  tff(f_86, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.47/2.31  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.47/2.31  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.47/2.31  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.47/2.31  tff(c_28, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.47/2.31  tff(c_76, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.47/2.31  tff(c_20, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.47/2.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.31  tff(c_885, plain, (![A_141, B_142]: (k5_xboole_0(k5_xboole_0(A_141, B_142), k3_xboole_0(A_141, B_142))=k2_xboole_0(A_141, B_142))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.47/2.31  tff(c_5167, plain, (![A_14844, B_14845]: (k5_xboole_0(k5_xboole_0(A_14844, B_14845), k3_xboole_0(B_14845, A_14844))=k2_xboole_0(A_14844, B_14845))), inference(superposition, [status(thm), theory('equality')], [c_2, c_885])).
% 6.47/2.31  tff(c_30, plain, (![A_22, B_23, C_24]: (k5_xboole_0(k5_xboole_0(A_22, B_23), C_24)=k5_xboole_0(A_22, k5_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.47/2.31  tff(c_5198, plain, (![A_14844, B_14845]: (k5_xboole_0(A_14844, k5_xboole_0(B_14845, k3_xboole_0(B_14845, A_14844)))=k2_xboole_0(A_14844, B_14845))), inference(superposition, [status(thm), theory('equality')], [c_5167, c_30])).
% 6.47/2.31  tff(c_5351, plain, (![A_15011, B_15012]: (k5_xboole_0(A_15011, k4_xboole_0(B_15012, A_15011))=k2_xboole_0(A_15011, B_15012))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_5198])).
% 6.47/2.31  tff(c_155, plain, (![B_80, A_81]: (k5_xboole_0(B_80, A_81)=k5_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.31  tff(c_171, plain, (![A_81]: (k5_xboole_0(k1_xboole_0, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_155, c_28])).
% 6.47/2.31  tff(c_32, plain, (![A_25]: (k5_xboole_0(A_25, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.47/2.31  tff(c_613, plain, (![A_127, B_128, C_129]: (k5_xboole_0(k5_xboole_0(A_127, B_128), C_129)=k5_xboole_0(A_127, k5_xboole_0(B_128, C_129)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.47/2.31  tff(c_670, plain, (![A_25, C_129]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_129))=k5_xboole_0(k1_xboole_0, C_129))), inference(superposition, [status(thm), theory('equality')], [c_32, c_613])).
% 6.47/2.31  tff(c_688, plain, (![A_25, C_129]: (k5_xboole_0(A_25, k5_xboole_0(A_25, C_129))=C_129)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_670])).
% 6.47/2.31  tff(c_5534, plain, (![A_15345, B_15346]: (k5_xboole_0(A_15345, k2_xboole_0(A_15345, B_15346))=k4_xboole_0(B_15346, A_15345))), inference(superposition, [status(thm), theory('equality')], [c_5351, c_688])).
% 6.47/2.31  tff(c_5601, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_5534])).
% 6.47/2.31  tff(c_5614, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5601])).
% 6.47/2.31  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.31  tff(c_694, plain, (![A_133, C_134]: (k5_xboole_0(A_133, k5_xboole_0(A_133, C_134))=C_134)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_670])).
% 6.47/2.31  tff(c_737, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_694])).
% 6.47/2.31  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.47/2.31  tff(c_317, plain, (![A_100, B_101]: (k3_xboole_0(A_100, B_101)=A_100 | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.31  tff(c_1315, plain, (![A_164, B_165]: (k3_xboole_0(k4_xboole_0(A_164, B_165), A_164)=k4_xboole_0(A_164, B_165))), inference(resolution, [status(thm)], [c_26, c_317])).
% 6.47/2.31  tff(c_34, plain, (![A_26, B_27]: (k5_xboole_0(k5_xboole_0(A_26, B_27), k3_xboole_0(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.47/2.31  tff(c_1321, plain, (![A_164, B_165]: (k5_xboole_0(k5_xboole_0(k4_xboole_0(A_164, B_165), A_164), k4_xboole_0(A_164, B_165))=k2_xboole_0(k4_xboole_0(A_164, B_165), A_164))), inference(superposition, [status(thm), theory('equality')], [c_1315, c_34])).
% 6.47/2.31  tff(c_1366, plain, (![A_164, B_165]: (k2_xboole_0(k4_xboole_0(A_164, B_165), A_164)=A_164)), inference(demodulation, [status(thm), theory('equality')], [c_737, c_4, c_4, c_1321])).
% 6.47/2.31  tff(c_5660, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5614, c_1366])).
% 6.47/2.31  tff(c_5896, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5660, c_76])).
% 6.47/2.31  tff(c_60, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.47/2.31  tff(c_254, plain, (![A_88, B_89]: (k1_enumset1(A_88, A_88, B_89)=k2_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.47/2.31  tff(c_40, plain, (![E_34, A_28, C_30]: (r2_hidden(E_34, k1_enumset1(A_28, E_34, C_30)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.47/2.31  tff(c_272, plain, (![A_90, B_91]: (r2_hidden(A_90, k2_tarski(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_254, c_40])).
% 6.47/2.31  tff(c_275, plain, (![A_35]: (r2_hidden(A_35, k1_tarski(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_272])).
% 6.47/2.31  tff(c_18, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.47/2.31  tff(c_328, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_18, c_317])).
% 6.47/2.31  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.47/2.31  tff(c_531, plain, (![A_112, B_113, C_114]: (~r1_xboole_0(A_112, B_113) | ~r2_hidden(C_114, k3_xboole_0(A_112, B_113)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.47/2.31  tff(c_568, plain, (![B_117, C_118]: (~r1_xboole_0(B_117, B_117) | ~r2_hidden(C_118, B_117))), inference(superposition, [status(thm), theory('equality')], [c_328, c_531])).
% 6.47/2.31  tff(c_571, plain, (![C_118, B_6]: (~r2_hidden(C_118, B_6) | k3_xboole_0(B_6, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_568])).
% 6.47/2.31  tff(c_575, plain, (![C_119, B_120]: (~r2_hidden(C_119, B_120) | k1_xboole_0!=B_120)), inference(demodulation, [status(thm), theory('equality')], [c_328, c_571])).
% 6.47/2.31  tff(c_595, plain, (![A_35]: (k1_tarski(A_35)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_275, c_575])).
% 6.47/2.31  tff(c_5922, plain, (![A_35]: (k1_tarski(A_35)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_595])).
% 6.47/2.31  tff(c_5666, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5614, c_26])).
% 6.47/2.31  tff(c_1330, plain, (![A_164, B_165]: (k5_xboole_0(k4_xboole_0(A_164, B_165), k4_xboole_0(A_164, B_165))=k4_xboole_0(k4_xboole_0(A_164, B_165), A_164))), inference(superposition, [status(thm), theory('equality')], [c_1315, c_20])).
% 6.47/2.31  tff(c_1367, plain, (![A_164, B_165]: (k4_xboole_0(k4_xboole_0(A_164, B_165), A_164)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1330])).
% 6.47/2.31  tff(c_5657, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5614, c_1367])).
% 6.47/2.31  tff(c_6585, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5896, c_5657])).
% 6.47/2.31  tff(c_465, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.47/2.31  tff(c_472, plain, (![A_19, B_20]: (k4_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_26, c_465])).
% 6.47/2.31  tff(c_6595, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6585, c_472])).
% 6.47/2.31  tff(c_6641, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5666, c_6585, c_6595])).
% 6.47/2.31  tff(c_6643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5922, c_6641])).
% 6.47/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.31  
% 6.47/2.31  Inference rules
% 6.47/2.31  ----------------------
% 6.47/2.31  #Ref     : 0
% 6.47/2.31  #Sup     : 1225
% 6.47/2.31  #Fact    : 18
% 6.47/2.31  #Define  : 0
% 6.47/2.31  #Split   : 1
% 6.47/2.31  #Chain   : 0
% 6.47/2.31  #Close   : 0
% 6.47/2.31  
% 6.47/2.31  Ordering : KBO
% 6.47/2.31  
% 6.47/2.31  Simplification rules
% 6.47/2.31  ----------------------
% 6.47/2.31  #Subsume      : 110
% 6.47/2.31  #Demod        : 728
% 6.47/2.31  #Tautology    : 588
% 6.47/2.31  #SimpNegUnit  : 17
% 6.47/2.31  #BackRed      : 27
% 6.47/2.31  
% 6.47/2.31  #Partial instantiations: 6042
% 6.47/2.31  #Strategies tried      : 1
% 6.47/2.31  
% 6.47/2.31  Timing (in seconds)
% 6.47/2.31  ----------------------
% 6.47/2.31  Preprocessing        : 0.35
% 6.47/2.31  Parsing              : 0.19
% 6.47/2.31  CNF conversion       : 0.03
% 6.47/2.31  Main loop            : 1.19
% 6.47/2.31  Inferencing          : 0.52
% 6.47/2.31  Reduction            : 0.41
% 6.47/2.31  Demodulation         : 0.34
% 6.47/2.31  BG Simplification    : 0.05
% 6.47/2.31  Subsumption          : 0.15
% 6.47/2.31  Abstraction          : 0.06
% 6.47/2.31  MUC search           : 0.00
% 6.47/2.31  Cooper               : 0.00
% 6.47/2.31  Total                : 1.57
% 6.47/2.31  Index Insertion      : 0.00
% 6.47/2.31  Index Deletion       : 0.00
% 6.47/2.31  Index Matching       : 0.00
% 6.47/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
