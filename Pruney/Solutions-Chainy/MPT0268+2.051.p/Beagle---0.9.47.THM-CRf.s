%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:40 EST 2020

% Result     : Theorem 6.32s
% Output     : CNFRefutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 129 expanded)
%              Number of leaves         :   35 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  109 ( 195 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_70,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_101,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_30,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_140,plain,(
    ! [D_65,B_66,A_67] :
      ( r2_hidden(D_65,B_66)
      | ~ r2_hidden(D_65,k3_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_145,plain,(
    ! [A_67,B_66] :
      ( r2_hidden('#skF_4'(k3_xboole_0(A_67,B_66)),B_66)
      | k3_xboole_0(A_67,B_66) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_140])).

tff(c_32,plain,(
    ! [A_17,B_18] : r1_xboole_0(k4_xboole_0(A_17,B_18),B_18) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_177,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,B_75)
      | ~ r2_hidden(C_76,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_202,plain,(
    ! [C_79,B_80,A_81] :
      ( ~ r2_hidden(C_79,B_80)
      | ~ r2_hidden(C_79,k4_xboole_0(A_81,B_80)) ) ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_565,plain,(
    ! [A_124,B_125] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_124,B_125)),B_125)
      | k4_xboole_0(A_124,B_125) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_202])).

tff(c_572,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_4'(A_16),k1_xboole_0)
      | k4_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_565])).

tff(c_575,plain,(
    ! [A_126] :
      ( ~ r2_hidden('#skF_4'(A_126),k1_xboole_0)
      | k1_xboole_0 = A_126 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_572])).

tff(c_619,plain,(
    ! [A_128] : k3_xboole_0(A_128,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_575])).

tff(c_28,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_636,plain,(
    ! [A_128] : k5_xboole_0(A_128,k1_xboole_0) = k4_xboole_0(A_128,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_28])).

tff(c_652,plain,(
    ! [A_128] : k5_xboole_0(A_128,k1_xboole_0) = A_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_636])).

tff(c_66,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(k1_tarski(A_36),B_37)
      | r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_335,plain,(
    ! [C_99,B_100,A_101] :
      ( ~ r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,k1_tarski(A_101))
      | r2_hidden(A_101,B_100) ) ),
    inference(resolution,[status(thm)],[c_66,c_177])).

tff(c_504,plain,(
    ! [A_115,A_116] :
      ( ~ r2_hidden('#skF_4'(A_115),k1_tarski(A_116))
      | r2_hidden(A_116,A_115)
      | k1_xboole_0 = A_115 ) ),
    inference(resolution,[status(thm)],[c_26,c_335])).

tff(c_12274,plain,(
    ! [A_4911,A_4912] :
      ( r2_hidden(A_4911,k3_xboole_0(A_4912,k1_tarski(A_4911)))
      | k3_xboole_0(A_4912,k1_tarski(A_4911)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_145,c_504])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12296,plain,(
    ! [A_4913,A_4914] :
      ( r2_hidden(A_4913,A_4914)
      | k3_xboole_0(A_4914,k1_tarski(A_4913)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12274,c_6])).

tff(c_12333,plain,(
    ! [A_4914,A_4913] :
      ( k4_xboole_0(A_4914,k1_tarski(A_4913)) = k5_xboole_0(A_4914,k1_xboole_0)
      | r2_hidden(A_4913,A_4914) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12296,c_28])).

tff(c_12358,plain,(
    ! [A_4915,A_4916] :
      ( k4_xboole_0(A_4915,k1_tarski(A_4916)) = A_4915
      | r2_hidden(A_4916,A_4915) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_12333])).

tff(c_68,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_133,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_12378,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12358,c_133])).

tff(c_12399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_12378])).

tff(c_12400,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_58,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_103,plain,(
    ! [A_53,B_54] : k1_enumset1(A_53,A_53,B_54) = k2_tarski(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    ! [E_25,A_19,B_20] : r2_hidden(E_25,k1_enumset1(A_19,B_20,E_25)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    ! [B_55,A_56] : r2_hidden(B_55,k2_tarski(A_56,B_55)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_36])).

tff(c_124,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_121])).

tff(c_12401,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0('#skF_7',k1_tarski('#skF_8')) != '#skF_7'
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12453,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12401,c_72])).

tff(c_12457,plain,(
    r1_xboole_0('#skF_9',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12453,c_32])).

tff(c_12461,plain,(
    ! [A_4929,B_4930,C_4931] :
      ( ~ r1_xboole_0(A_4929,B_4930)
      | ~ r2_hidden(C_4931,B_4930)
      | ~ r2_hidden(C_4931,A_4929) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12492,plain,(
    ! [C_4934] :
      ( ~ r2_hidden(C_4934,k1_tarski('#skF_10'))
      | ~ r2_hidden(C_4934,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12457,c_12461])).

tff(c_12504,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_124,c_12492])).

tff(c_12514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12400,c_12504])).

tff(c_12515,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_12518,plain,(
    ! [A_4938,B_4939] : k1_enumset1(A_4938,A_4938,B_4939) = k2_tarski(A_4938,B_4939) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12536,plain,(
    ! [B_4940,A_4941] : r2_hidden(B_4940,k2_tarski(A_4941,B_4940)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12518,c_36])).

tff(c_12539,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_12536])).

tff(c_12516,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_8','#skF_7')
    | k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12584,plain,(
    k4_xboole_0('#skF_9',k1_tarski('#skF_10')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12516,c_74])).

tff(c_12588,plain,(
    r1_xboole_0('#skF_9',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12584,c_32])).

tff(c_12602,plain,(
    ! [A_4959,B_4960,C_4961] :
      ( ~ r1_xboole_0(A_4959,B_4960)
      | ~ r2_hidden(C_4961,B_4960)
      | ~ r2_hidden(C_4961,A_4959) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12630,plain,(
    ! [C_4964] :
      ( ~ r2_hidden(C_4964,k1_tarski('#skF_10'))
      | ~ r2_hidden(C_4964,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12588,c_12602])).

tff(c_12642,plain,(
    ~ r2_hidden('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_12539,c_12630])).

tff(c_12652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12515,c_12642])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.32/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.36  
% 6.32/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.36  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5
% 6.32/2.36  
% 6.32/2.36  %Foreground sorts:
% 6.32/2.36  
% 6.32/2.36  
% 6.32/2.36  %Background operators:
% 6.32/2.36  
% 6.32/2.36  
% 6.32/2.36  %Foreground operators:
% 6.32/2.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.32/2.36  tff('#skF_4', type, '#skF_4': $i > $i).
% 6.32/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.32/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.32/2.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.32/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.32/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.32/2.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.32/2.36  tff('#skF_7', type, '#skF_7': $i).
% 6.32/2.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.32/2.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.32/2.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.32/2.36  tff('#skF_10', type, '#skF_10': $i).
% 6.32/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.32/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.32/2.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.32/2.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.32/2.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.32/2.36  tff('#skF_9', type, '#skF_9': $i).
% 6.32/2.36  tff('#skF_8', type, '#skF_8': $i).
% 6.32/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.32/2.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.32/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.32/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.32/2.36  
% 6.32/2.38  tff(f_100, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.32/2.38  tff(f_64, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.32/2.38  tff(f_60, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.32/2.38  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.32/2.38  tff(f_66, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.32/2.38  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.32/2.38  tff(f_62, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.32/2.38  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 6.32/2.38  tff(f_83, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.32/2.38  tff(f_85, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.32/2.38  tff(f_81, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.32/2.38  tff(c_70, plain, (~r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.32/2.38  tff(c_101, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 6.32/2.38  tff(c_30, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.32/2.38  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.32/2.38  tff(c_140, plain, (![D_65, B_66, A_67]: (r2_hidden(D_65, B_66) | ~r2_hidden(D_65, k3_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.32/2.38  tff(c_145, plain, (![A_67, B_66]: (r2_hidden('#skF_4'(k3_xboole_0(A_67, B_66)), B_66) | k3_xboole_0(A_67, B_66)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_140])).
% 6.32/2.38  tff(c_32, plain, (![A_17, B_18]: (r1_xboole_0(k4_xboole_0(A_17, B_18), B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.32/2.38  tff(c_177, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, B_75) | ~r2_hidden(C_76, A_74))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.32/2.38  tff(c_202, plain, (![C_79, B_80, A_81]: (~r2_hidden(C_79, B_80) | ~r2_hidden(C_79, k4_xboole_0(A_81, B_80)))), inference(resolution, [status(thm)], [c_32, c_177])).
% 6.32/2.38  tff(c_565, plain, (![A_124, B_125]: (~r2_hidden('#skF_4'(k4_xboole_0(A_124, B_125)), B_125) | k4_xboole_0(A_124, B_125)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_202])).
% 6.32/2.38  tff(c_572, plain, (![A_16]: (~r2_hidden('#skF_4'(A_16), k1_xboole_0) | k4_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_565])).
% 6.32/2.38  tff(c_575, plain, (![A_126]: (~r2_hidden('#skF_4'(A_126), k1_xboole_0) | k1_xboole_0=A_126)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_572])).
% 6.32/2.38  tff(c_619, plain, (![A_128]: (k3_xboole_0(A_128, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_145, c_575])).
% 6.32/2.38  tff(c_28, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.32/2.38  tff(c_636, plain, (![A_128]: (k5_xboole_0(A_128, k1_xboole_0)=k4_xboole_0(A_128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_619, c_28])).
% 6.32/2.38  tff(c_652, plain, (![A_128]: (k5_xboole_0(A_128, k1_xboole_0)=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_636])).
% 6.32/2.38  tff(c_66, plain, (![A_36, B_37]: (r1_xboole_0(k1_tarski(A_36), B_37) | r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.32/2.38  tff(c_335, plain, (![C_99, B_100, A_101]: (~r2_hidden(C_99, B_100) | ~r2_hidden(C_99, k1_tarski(A_101)) | r2_hidden(A_101, B_100))), inference(resolution, [status(thm)], [c_66, c_177])).
% 6.32/2.38  tff(c_504, plain, (![A_115, A_116]: (~r2_hidden('#skF_4'(A_115), k1_tarski(A_116)) | r2_hidden(A_116, A_115) | k1_xboole_0=A_115)), inference(resolution, [status(thm)], [c_26, c_335])).
% 6.32/2.38  tff(c_12274, plain, (![A_4911, A_4912]: (r2_hidden(A_4911, k3_xboole_0(A_4912, k1_tarski(A_4911))) | k3_xboole_0(A_4912, k1_tarski(A_4911))=k1_xboole_0)), inference(resolution, [status(thm)], [c_145, c_504])).
% 6.32/2.38  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.32/2.38  tff(c_12296, plain, (![A_4913, A_4914]: (r2_hidden(A_4913, A_4914) | k3_xboole_0(A_4914, k1_tarski(A_4913))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12274, c_6])).
% 6.32/2.38  tff(c_12333, plain, (![A_4914, A_4913]: (k4_xboole_0(A_4914, k1_tarski(A_4913))=k5_xboole_0(A_4914, k1_xboole_0) | r2_hidden(A_4913, A_4914))), inference(superposition, [status(thm), theory('equality')], [c_12296, c_28])).
% 6.32/2.38  tff(c_12358, plain, (![A_4915, A_4916]: (k4_xboole_0(A_4915, k1_tarski(A_4916))=A_4915 | r2_hidden(A_4916, A_4915))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_12333])).
% 6.32/2.38  tff(c_68, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.32/2.38  tff(c_133, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_68])).
% 6.32/2.38  tff(c_12378, plain, (r2_hidden('#skF_8', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12358, c_133])).
% 6.32/2.38  tff(c_12399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_12378])).
% 6.32/2.38  tff(c_12400, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 6.32/2.38  tff(c_58, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.32/2.38  tff(c_103, plain, (![A_53, B_54]: (k1_enumset1(A_53, A_53, B_54)=k2_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.32/2.38  tff(c_36, plain, (![E_25, A_19, B_20]: (r2_hidden(E_25, k1_enumset1(A_19, B_20, E_25)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.32/2.38  tff(c_121, plain, (![B_55, A_56]: (r2_hidden(B_55, k2_tarski(A_56, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_36])).
% 6.32/2.38  tff(c_124, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_121])).
% 6.32/2.38  tff(c_12401, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_68])).
% 6.32/2.38  tff(c_72, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))!='#skF_7' | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.32/2.38  tff(c_12453, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_12401, c_72])).
% 6.32/2.38  tff(c_12457, plain, (r1_xboole_0('#skF_9', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_12453, c_32])).
% 6.32/2.38  tff(c_12461, plain, (![A_4929, B_4930, C_4931]: (~r1_xboole_0(A_4929, B_4930) | ~r2_hidden(C_4931, B_4930) | ~r2_hidden(C_4931, A_4929))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.32/2.38  tff(c_12492, plain, (![C_4934]: (~r2_hidden(C_4934, k1_tarski('#skF_10')) | ~r2_hidden(C_4934, '#skF_9'))), inference(resolution, [status(thm)], [c_12457, c_12461])).
% 6.32/2.38  tff(c_12504, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_124, c_12492])).
% 6.32/2.38  tff(c_12514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12400, c_12504])).
% 6.32/2.38  tff(c_12515, plain, (r2_hidden('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_70])).
% 6.32/2.38  tff(c_12518, plain, (![A_4938, B_4939]: (k1_enumset1(A_4938, A_4938, B_4939)=k2_tarski(A_4938, B_4939))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.32/2.38  tff(c_12536, plain, (![B_4940, A_4941]: (r2_hidden(B_4940, k2_tarski(A_4941, B_4940)))), inference(superposition, [status(thm), theory('equality')], [c_12518, c_36])).
% 6.32/2.38  tff(c_12539, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_12536])).
% 6.32/2.38  tff(c_12516, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 6.32/2.38  tff(c_74, plain, (~r2_hidden('#skF_8', '#skF_7') | k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.32/2.38  tff(c_12584, plain, (k4_xboole_0('#skF_9', k1_tarski('#skF_10'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_12516, c_74])).
% 6.32/2.38  tff(c_12588, plain, (r1_xboole_0('#skF_9', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_12584, c_32])).
% 6.32/2.38  tff(c_12602, plain, (![A_4959, B_4960, C_4961]: (~r1_xboole_0(A_4959, B_4960) | ~r2_hidden(C_4961, B_4960) | ~r2_hidden(C_4961, A_4959))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.32/2.38  tff(c_12630, plain, (![C_4964]: (~r2_hidden(C_4964, k1_tarski('#skF_10')) | ~r2_hidden(C_4964, '#skF_9'))), inference(resolution, [status(thm)], [c_12588, c_12602])).
% 6.32/2.38  tff(c_12642, plain, (~r2_hidden('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_12539, c_12630])).
% 6.32/2.38  tff(c_12652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12515, c_12642])).
% 6.32/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.32/2.38  
% 6.32/2.38  Inference rules
% 6.32/2.38  ----------------------
% 6.32/2.38  #Ref     : 0
% 6.32/2.38  #Sup     : 2242
% 6.32/2.38  #Fact    : 2
% 6.32/2.38  #Define  : 0
% 6.32/2.38  #Split   : 2
% 6.32/2.38  #Chain   : 0
% 6.32/2.38  #Close   : 0
% 6.32/2.38  
% 6.32/2.38  Ordering : KBO
% 6.32/2.38  
% 6.32/2.38  Simplification rules
% 6.32/2.38  ----------------------
% 6.32/2.38  #Subsume      : 607
% 6.32/2.38  #Demod        : 513
% 6.32/2.38  #Tautology    : 148
% 6.32/2.38  #SimpNegUnit  : 1
% 6.32/2.38  #BackRed      : 0
% 6.32/2.38  
% 6.32/2.38  #Partial instantiations: 2318
% 6.32/2.38  #Strategies tried      : 1
% 6.32/2.38  
% 6.32/2.38  Timing (in seconds)
% 6.32/2.38  ----------------------
% 6.32/2.38  Preprocessing        : 0.33
% 6.32/2.38  Parsing              : 0.17
% 6.32/2.38  CNF conversion       : 0.03
% 6.32/2.38  Main loop            : 1.27
% 6.32/2.38  Inferencing          : 0.50
% 6.32/2.38  Reduction            : 0.34
% 6.32/2.38  Demodulation         : 0.25
% 6.32/2.38  BG Simplification    : 0.07
% 6.32/2.38  Subsumption          : 0.26
% 6.32/2.39  Abstraction          : 0.09
% 6.32/2.39  MUC search           : 0.00
% 6.32/2.39  Cooper               : 0.00
% 6.32/2.39  Total                : 1.63
% 6.32/2.39  Index Insertion      : 0.00
% 6.32/2.39  Index Deletion       : 0.00
% 6.32/2.39  Index Matching       : 0.00
% 6.32/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
