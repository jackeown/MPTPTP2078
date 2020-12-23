%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:51 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 131 expanded)
%              Number of leaves         :   40 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :   70 ( 121 expanded)
%              Number of equality atoms :   46 (  91 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_16,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_307,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_315,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_307])).

tff(c_135,plain,(
    ! [B_78,A_79] : k5_xboole_0(B_78,A_79) = k5_xboole_0(A_79,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_151,plain,(
    ! [A_79] : k5_xboole_0(k1_xboole_0,A_79) = A_79 ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_20])).

tff(c_262,plain,(
    ! [A_89,B_90] : r1_xboole_0(k3_xboole_0(A_89,B_90),k5_xboole_0(A_89,B_90)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_265,plain,(
    ! [A_79] : r1_xboole_0(k3_xboole_0(k1_xboole_0,A_79),A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_262])).

tff(c_316,plain,(
    ! [A_79] : r1_xboole_0(k1_xboole_0,A_79) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_265])).

tff(c_444,plain,(
    ! [A_102,B_103,C_104] :
      ( ~ r1_xboole_0(A_102,B_103)
      | ~ r2_hidden(C_104,k3_xboole_0(A_102,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_450,plain,(
    ! [A_16,C_104] :
      ( ~ r1_xboole_0(k1_xboole_0,A_16)
      | ~ r2_hidden(C_104,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_444])).

tff(c_458,plain,(
    ! [C_104] : ~ r2_hidden(C_104,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_450])).

tff(c_66,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_653,plain,(
    ! [A_117,B_118] : k5_xboole_0(k5_xboole_0(A_117,B_118),k3_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7109,plain,(
    ! [A_14421,B_14422] : k5_xboole_0(k3_xboole_0(A_14421,B_14422),k5_xboole_0(A_14421,B_14422)) = k2_xboole_0(A_14421,B_14422) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_4])).

tff(c_541,plain,(
    ! [A_112,B_113,C_114] : k5_xboole_0(k5_xboole_0(A_112,B_113),C_114) = k5_xboole_0(A_112,k5_xboole_0(B_113,C_114)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_591,plain,(
    ! [B_4,A_112,B_113] : k5_xboole_0(B_4,k5_xboole_0(A_112,B_113)) = k5_xboole_0(A_112,k5_xboole_0(B_113,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_541])).

tff(c_7136,plain,(
    ! [B_14422,A_14421] : k5_xboole_0(B_14422,k5_xboole_0(k3_xboole_0(A_14421,B_14422),A_14421)) = k2_xboole_0(A_14421,B_14422) ),
    inference(superposition,[status(thm),theory(equality)],[c_7109,c_591])).

tff(c_7473,plain,(
    ! [B_14749,A_14750] : k5_xboole_0(B_14749,k4_xboole_0(A_14750,B_14749)) = k2_xboole_0(A_14750,B_14749) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4,c_7136])).

tff(c_24,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_608,plain,(
    ! [A_23,C_114] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_114)) = k5_xboole_0(k1_xboole_0,C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_541])).

tff(c_621,plain,(
    ! [A_23,C_114] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_114)) = C_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_608])).

tff(c_8302,plain,(
    ! [B_15893,A_15894] : k5_xboole_0(B_15893,k2_xboole_0(A_15894,B_15893)) = k4_xboole_0(A_15894,B_15893) ),
    inference(superposition,[status(thm),theory(equality)],[c_7473,c_621])).

tff(c_8417,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8302])).

tff(c_8436,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8417])).

tff(c_822,plain,(
    ! [A_124,C_125] : k5_xboole_0(A_124,k5_xboole_0(A_124,C_125)) = C_125 ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_608])).

tff(c_896,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k5_xboole_0(B_127,A_126)) = B_127 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_822])).

tff(c_935,plain,(
    ! [A_23,C_114] : k5_xboole_0(k5_xboole_0(A_23,C_114),C_114) = A_23 ),
    inference(superposition,[status(thm),theory(equality)],[c_621,c_896])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4310,plain,(
    ! [A_10646,B_10647] : k3_xboole_0(k4_xboole_0(A_10646,B_10647),A_10646) = k4_xboole_0(A_10646,B_10647) ),
    inference(resolution,[status(thm)],[c_18,c_307])).

tff(c_4569,plain,(
    ! [A_11304,B_11305] : k3_xboole_0(A_11304,k4_xboole_0(A_11304,B_11305)) = k4_xboole_0(A_11304,B_11305) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4310])).

tff(c_26,plain,(
    ! [A_24,B_25] : k5_xboole_0(k5_xboole_0(A_24,B_25),k3_xboole_0(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4593,plain,(
    ! [A_11304,B_11305] : k5_xboole_0(k5_xboole_0(A_11304,k4_xboole_0(A_11304,B_11305)),k4_xboole_0(A_11304,B_11305)) = k2_xboole_0(A_11304,k4_xboole_0(A_11304,B_11305)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4569,c_26])).

tff(c_4636,plain,(
    ! [A_11304,B_11305] : k2_xboole_0(A_11304,k4_xboole_0(A_11304,B_11305)) = A_11304 ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_4593])).

tff(c_8491,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8436,c_4636])).

tff(c_8523,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8491])).

tff(c_241,plain,(
    ! [A_83,B_84] : k1_enumset1(A_83,A_83,B_84) = k2_tarski(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [E_32,B_27,C_28] : r2_hidden(E_32,k1_enumset1(E_32,B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_250,plain,(
    ! [A_83,B_84] : r2_hidden(A_83,k2_tarski(A_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_34])).

tff(c_8538,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8523,c_250])).

tff(c_8548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_8538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.47/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.34  
% 6.47/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.47/2.34  
% 6.47/2.34  %Foreground sorts:
% 6.47/2.34  
% 6.47/2.34  
% 6.47/2.34  %Background operators:
% 6.47/2.34  
% 6.47/2.34  
% 6.47/2.34  %Foreground operators:
% 6.47/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.47/2.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.47/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.47/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.47/2.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.47/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.47/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.47/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.47/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.47/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.47/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.47/2.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.47/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.47/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.47/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.47/2.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.47/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.47/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.47/2.34  
% 6.47/2.36  tff(f_53, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.47/2.36  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.47/2.36  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.47/2.36  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.47/2.36  tff(f_45, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.47/2.36  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.47/2.36  tff(f_96, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 6.47/2.36  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.47/2.36  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.47/2.36  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.47/2.36  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.47/2.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.47/2.36  tff(f_55, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.47/2.36  tff(f_80, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.47/2.36  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.47/2.36  tff(c_16, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.47/2.36  tff(c_307, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.47/2.36  tff(c_315, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_307])).
% 6.47/2.36  tff(c_135, plain, (![B_78, A_79]: (k5_xboole_0(B_78, A_79)=k5_xboole_0(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.36  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.47/2.36  tff(c_151, plain, (![A_79]: (k5_xboole_0(k1_xboole_0, A_79)=A_79)), inference(superposition, [status(thm), theory('equality')], [c_135, c_20])).
% 6.47/2.36  tff(c_262, plain, (![A_89, B_90]: (r1_xboole_0(k3_xboole_0(A_89, B_90), k5_xboole_0(A_89, B_90)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.47/2.36  tff(c_265, plain, (![A_79]: (r1_xboole_0(k3_xboole_0(k1_xboole_0, A_79), A_79))), inference(superposition, [status(thm), theory('equality')], [c_151, c_262])).
% 6.47/2.36  tff(c_316, plain, (![A_79]: (r1_xboole_0(k1_xboole_0, A_79))), inference(demodulation, [status(thm), theory('equality')], [c_315, c_265])).
% 6.47/2.36  tff(c_444, plain, (![A_102, B_103, C_104]: (~r1_xboole_0(A_102, B_103) | ~r2_hidden(C_104, k3_xboole_0(A_102, B_103)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.47/2.36  tff(c_450, plain, (![A_16, C_104]: (~r1_xboole_0(k1_xboole_0, A_16) | ~r2_hidden(C_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_315, c_444])).
% 6.47/2.36  tff(c_458, plain, (![C_104]: (~r2_hidden(C_104, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_450])).
% 6.47/2.36  tff(c_66, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.47/2.36  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.47/2.36  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.36  tff(c_653, plain, (![A_117, B_118]: (k5_xboole_0(k5_xboole_0(A_117, B_118), k3_xboole_0(A_117, B_118))=k2_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.47/2.36  tff(c_7109, plain, (![A_14421, B_14422]: (k5_xboole_0(k3_xboole_0(A_14421, B_14422), k5_xboole_0(A_14421, B_14422))=k2_xboole_0(A_14421, B_14422))), inference(superposition, [status(thm), theory('equality')], [c_653, c_4])).
% 6.47/2.36  tff(c_541, plain, (![A_112, B_113, C_114]: (k5_xboole_0(k5_xboole_0(A_112, B_113), C_114)=k5_xboole_0(A_112, k5_xboole_0(B_113, C_114)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.47/2.36  tff(c_591, plain, (![B_4, A_112, B_113]: (k5_xboole_0(B_4, k5_xboole_0(A_112, B_113))=k5_xboole_0(A_112, k5_xboole_0(B_113, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_541])).
% 6.47/2.36  tff(c_7136, plain, (![B_14422, A_14421]: (k5_xboole_0(B_14422, k5_xboole_0(k3_xboole_0(A_14421, B_14422), A_14421))=k2_xboole_0(A_14421, B_14422))), inference(superposition, [status(thm), theory('equality')], [c_7109, c_591])).
% 6.47/2.36  tff(c_7473, plain, (![B_14749, A_14750]: (k5_xboole_0(B_14749, k4_xboole_0(A_14750, B_14749))=k2_xboole_0(A_14750, B_14749))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4, c_7136])).
% 6.47/2.36  tff(c_24, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.47/2.36  tff(c_608, plain, (![A_23, C_114]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_114))=k5_xboole_0(k1_xboole_0, C_114))), inference(superposition, [status(thm), theory('equality')], [c_24, c_541])).
% 6.47/2.36  tff(c_621, plain, (![A_23, C_114]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_114))=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_151, c_608])).
% 6.47/2.36  tff(c_8302, plain, (![B_15893, A_15894]: (k5_xboole_0(B_15893, k2_xboole_0(A_15894, B_15893))=k4_xboole_0(A_15894, B_15893))), inference(superposition, [status(thm), theory('equality')], [c_7473, c_621])).
% 6.47/2.36  tff(c_8417, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_66, c_8302])).
% 6.47/2.36  tff(c_8436, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8417])).
% 6.47/2.36  tff(c_822, plain, (![A_124, C_125]: (k5_xboole_0(A_124, k5_xboole_0(A_124, C_125))=C_125)), inference(demodulation, [status(thm), theory('equality')], [c_151, c_608])).
% 6.47/2.36  tff(c_896, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k5_xboole_0(B_127, A_126))=B_127)), inference(superposition, [status(thm), theory('equality')], [c_4, c_822])).
% 6.47/2.36  tff(c_935, plain, (![A_23, C_114]: (k5_xboole_0(k5_xboole_0(A_23, C_114), C_114)=A_23)), inference(superposition, [status(thm), theory('equality')], [c_621, c_896])).
% 6.47/2.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.36  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.47/2.36  tff(c_4310, plain, (![A_10646, B_10647]: (k3_xboole_0(k4_xboole_0(A_10646, B_10647), A_10646)=k4_xboole_0(A_10646, B_10647))), inference(resolution, [status(thm)], [c_18, c_307])).
% 6.47/2.36  tff(c_4569, plain, (![A_11304, B_11305]: (k3_xboole_0(A_11304, k4_xboole_0(A_11304, B_11305))=k4_xboole_0(A_11304, B_11305))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4310])).
% 6.47/2.36  tff(c_26, plain, (![A_24, B_25]: (k5_xboole_0(k5_xboole_0(A_24, B_25), k3_xboole_0(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.47/2.36  tff(c_4593, plain, (![A_11304, B_11305]: (k5_xboole_0(k5_xboole_0(A_11304, k4_xboole_0(A_11304, B_11305)), k4_xboole_0(A_11304, B_11305))=k2_xboole_0(A_11304, k4_xboole_0(A_11304, B_11305)))), inference(superposition, [status(thm), theory('equality')], [c_4569, c_26])).
% 6.47/2.36  tff(c_4636, plain, (![A_11304, B_11305]: (k2_xboole_0(A_11304, k4_xboole_0(A_11304, B_11305))=A_11304)), inference(demodulation, [status(thm), theory('equality')], [c_935, c_4593])).
% 6.47/2.36  tff(c_8491, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8436, c_4636])).
% 6.47/2.36  tff(c_8523, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8491])).
% 6.47/2.36  tff(c_241, plain, (![A_83, B_84]: (k1_enumset1(A_83, A_83, B_84)=k2_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.47/2.36  tff(c_34, plain, (![E_32, B_27, C_28]: (r2_hidden(E_32, k1_enumset1(E_32, B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.47/2.36  tff(c_250, plain, (![A_83, B_84]: (r2_hidden(A_83, k2_tarski(A_83, B_84)))), inference(superposition, [status(thm), theory('equality')], [c_241, c_34])).
% 6.47/2.36  tff(c_8538, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8523, c_250])).
% 6.47/2.36  tff(c_8548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_458, c_8538])).
% 6.47/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.36  
% 6.47/2.36  Inference rules
% 6.47/2.36  ----------------------
% 6.47/2.36  #Ref     : 0
% 6.47/2.36  #Sup     : 1715
% 6.47/2.36  #Fact    : 18
% 6.47/2.36  #Define  : 0
% 6.47/2.36  #Split   : 0
% 6.47/2.36  #Chain   : 0
% 6.47/2.36  #Close   : 0
% 6.47/2.36  
% 6.47/2.36  Ordering : KBO
% 6.47/2.36  
% 6.47/2.36  Simplification rules
% 6.47/2.36  ----------------------
% 6.47/2.36  #Subsume      : 108
% 6.47/2.36  #Demod        : 1427
% 6.47/2.36  #Tautology    : 872
% 6.47/2.36  #SimpNegUnit  : 12
% 6.47/2.36  #BackRed      : 7
% 6.47/2.36  
% 6.47/2.36  #Partial instantiations: 5643
% 6.47/2.36  #Strategies tried      : 1
% 6.47/2.36  
% 6.47/2.36  Timing (in seconds)
% 6.47/2.36  ----------------------
% 6.47/2.36  Preprocessing        : 0.33
% 6.47/2.36  Parsing              : 0.18
% 6.47/2.36  CNF conversion       : 0.02
% 6.47/2.36  Main loop            : 1.26
% 6.47/2.36  Inferencing          : 0.55
% 6.47/2.36  Reduction            : 0.47
% 6.47/2.36  Demodulation         : 0.40
% 6.47/2.36  BG Simplification    : 0.05
% 6.47/2.36  Subsumption          : 0.15
% 6.47/2.36  Abstraction          : 0.06
% 6.47/2.36  MUC search           : 0.00
% 6.47/2.36  Cooper               : 0.00
% 6.47/2.36  Total                : 1.63
% 6.47/2.36  Index Insertion      : 0.00
% 6.47/2.36  Index Deletion       : 0.00
% 6.47/2.36  Index Matching       : 0.00
% 6.47/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
