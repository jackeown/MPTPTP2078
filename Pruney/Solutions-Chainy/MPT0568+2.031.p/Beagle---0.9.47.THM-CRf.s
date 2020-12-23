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
% DateTime   : Thu Dec  3 10:01:24 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 137 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 153 expanded)
%              Number of equality atoms :   56 ( 124 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_76,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_44,plain,(
    ! [A_44] : k2_relat_1(k6_relat_1(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_39] : v1_relat_1(k6_relat_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,(
    ! [A_53] :
      ( k2_relat_1(A_53) != k1_xboole_0
      | k1_xboole_0 = A_53
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_133,plain,(
    ! [A_39] :
      ( k2_relat_1(k6_relat_1(A_39)) != k1_xboole_0
      | k6_relat_1(A_39) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_130])).

tff(c_137,plain,(
    ! [A_54] :
      ( k1_xboole_0 != A_54
      | k6_relat_1(A_54) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_133])).

tff(c_148,plain,(
    ! [A_54] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_28])).

tff(c_156,plain,(
    ! [A_54] : k1_xboole_0 != A_54 ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_8])).

tff(c_164,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_225,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_216])).

tff(c_251,plain,(
    ! [A_65] : k2_xboole_0(A_65,k1_xboole_0) = A_65 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_225])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_257,plain,(
    ! [A_65] : k2_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_2])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_212,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_203])).

tff(c_229,plain,(
    ! [A_64] : k4_xboole_0(A_64,k1_xboole_0) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_212])).

tff(c_12,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_235,plain,(
    ! [A_64] : k5_xboole_0(k1_xboole_0,A_64) = k2_xboole_0(k1_xboole_0,A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_12])).

tff(c_359,plain,(
    ! [A_72] : k5_xboole_0(k1_xboole_0,A_72) = A_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_235])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_370,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k3_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_4])).

tff(c_392,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_370])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_454,plain,(
    ! [B_79,A_80] :
      ( k10_relat_1(B_79,k3_xboole_0(k2_relat_1(B_79),A_80)) = k10_relat_1(B_79,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,(
    ! [A_39] :
      ( k1_xboole_0 != A_39
      | k6_relat_1(A_39) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_133])).

tff(c_42,plain,(
    ! [A_44] : k1_relat_1(k6_relat_1(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_313,plain,(
    ! [A_67] :
      ( k10_relat_1(A_67,k2_relat_1(A_67)) = k1_relat_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_322,plain,(
    ! [A_44] :
      ( k10_relat_1(k6_relat_1(A_44),A_44) = k1_relat_1(k6_relat_1(A_44))
      | ~ v1_relat_1(k6_relat_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_313])).

tff(c_337,plain,(
    ! [A_68] : k10_relat_1(k6_relat_1(A_68),A_68) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_322])).

tff(c_346,plain,(
    ! [A_39] :
      ( k10_relat_1(k1_xboole_0,A_39) = A_39
      | k1_xboole_0 != A_39 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_337])).

tff(c_461,plain,(
    ! [A_80] :
      ( k3_xboole_0(k2_relat_1(k1_xboole_0),A_80) = k10_relat_1(k1_xboole_0,A_80)
      | k3_xboole_0(k2_relat_1(k1_xboole_0),A_80) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_346])).

tff(c_481,plain,(
    ! [A_80] : k10_relat_1(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_392,c_34,c_392,c_34,c_461])).

tff(c_46,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:13:08 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.27  
% 2.15/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.27  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.15/1.27  
% 2.15/1.27  %Foreground sorts:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Background operators:
% 2.15/1.27  
% 2.15/1.27  
% 2.15/1.27  %Foreground operators:
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.15/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.15/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.15/1.27  
% 2.15/1.29  tff(f_76, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.15/1.29  tff(f_53, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.15/1.29  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.15/1.29  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.15/1.29  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.15/1.29  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.15/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.15/1.29  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.15/1.29  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.15/1.29  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.15/1.29  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.15/1.29  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.15/1.29  tff(f_79, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.15/1.29  tff(c_44, plain, (![A_44]: (k2_relat_1(k6_relat_1(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.29  tff(c_28, plain, (![A_39]: (v1_relat_1(k6_relat_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.29  tff(c_130, plain, (![A_53]: (k2_relat_1(A_53)!=k1_xboole_0 | k1_xboole_0=A_53 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.15/1.29  tff(c_133, plain, (![A_39]: (k2_relat_1(k6_relat_1(A_39))!=k1_xboole_0 | k6_relat_1(A_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_130])).
% 2.15/1.29  tff(c_137, plain, (![A_54]: (k1_xboole_0!=A_54 | k6_relat_1(A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_133])).
% 2.15/1.29  tff(c_148, plain, (![A_54]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_54)), inference(superposition, [status(thm), theory('equality')], [c_137, c_28])).
% 2.15/1.29  tff(c_156, plain, (![A_54]: (k1_xboole_0!=A_54)), inference(splitLeft, [status(thm)], [c_148])).
% 2.15/1.29  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.29  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_8])).
% 2.15/1.29  tff(c_164, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_148])).
% 2.15/1.29  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.29  tff(c_216, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k4_xboole_0(B_63, A_62))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.29  tff(c_225, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_216])).
% 2.15/1.29  tff(c_251, plain, (![A_65]: (k2_xboole_0(A_65, k1_xboole_0)=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_225])).
% 2.15/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.29  tff(c_257, plain, (![A_65]: (k2_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_251, c_2])).
% 2.15/1.29  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.29  tff(c_203, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.15/1.29  tff(c_212, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_203])).
% 2.15/1.29  tff(c_229, plain, (![A_64]: (k4_xboole_0(A_64, k1_xboole_0)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_212])).
% 2.15/1.29  tff(c_12, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.29  tff(c_235, plain, (![A_64]: (k5_xboole_0(k1_xboole_0, A_64)=k2_xboole_0(k1_xboole_0, A_64))), inference(superposition, [status(thm), theory('equality')], [c_229, c_12])).
% 2.15/1.29  tff(c_359, plain, (![A_72]: (k5_xboole_0(k1_xboole_0, A_72)=A_72)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_235])).
% 2.15/1.29  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.15/1.29  tff(c_370, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k3_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_359, c_4])).
% 2.15/1.29  tff(c_392, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_370])).
% 2.15/1.29  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.15/1.29  tff(c_454, plain, (![B_79, A_80]: (k10_relat_1(B_79, k3_xboole_0(k2_relat_1(B_79), A_80))=k10_relat_1(B_79, A_80) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.15/1.29  tff(c_135, plain, (![A_39]: (k1_xboole_0!=A_39 | k6_relat_1(A_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_133])).
% 2.15/1.29  tff(c_42, plain, (![A_44]: (k1_relat_1(k6_relat_1(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.15/1.29  tff(c_313, plain, (![A_67]: (k10_relat_1(A_67, k2_relat_1(A_67))=k1_relat_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.29  tff(c_322, plain, (![A_44]: (k10_relat_1(k6_relat_1(A_44), A_44)=k1_relat_1(k6_relat_1(A_44)) | ~v1_relat_1(k6_relat_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_313])).
% 2.15/1.29  tff(c_337, plain, (![A_68]: (k10_relat_1(k6_relat_1(A_68), A_68)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_322])).
% 2.15/1.29  tff(c_346, plain, (![A_39]: (k10_relat_1(k1_xboole_0, A_39)=A_39 | k1_xboole_0!=A_39)), inference(superposition, [status(thm), theory('equality')], [c_135, c_337])).
% 2.15/1.29  tff(c_461, plain, (![A_80]: (k3_xboole_0(k2_relat_1(k1_xboole_0), A_80)=k10_relat_1(k1_xboole_0, A_80) | k3_xboole_0(k2_relat_1(k1_xboole_0), A_80)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_454, c_346])).
% 2.15/1.29  tff(c_481, plain, (![A_80]: (k10_relat_1(k1_xboole_0, A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_392, c_34, c_392, c_34, c_461])).
% 2.15/1.29  tff(c_46, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.15/1.29  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_46])).
% 2.15/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  Inference rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Ref     : 0
% 2.15/1.29  #Sup     : 98
% 2.15/1.29  #Fact    : 0
% 2.15/1.29  #Define  : 0
% 2.15/1.29  #Split   : 2
% 2.15/1.29  #Chain   : 0
% 2.15/1.29  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 4
% 2.15/1.29  #Demod        : 54
% 2.15/1.29  #Tautology    : 84
% 2.15/1.29  #SimpNegUnit  : 6
% 2.15/1.29  #BackRed      : 5
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.29  Preprocessing        : 0.32
% 2.15/1.29  Parsing              : 0.17
% 2.15/1.29  CNF conversion       : 0.02
% 2.15/1.29  Main loop            : 0.20
% 2.15/1.29  Inferencing          : 0.08
% 2.15/1.29  Reduction            : 0.07
% 2.15/1.29  Demodulation         : 0.05
% 2.15/1.29  BG Simplification    : 0.02
% 2.15/1.29  Subsumption          : 0.02
% 2.15/1.29  Abstraction          : 0.01
% 2.15/1.29  MUC search           : 0.00
% 2.15/1.29  Cooper               : 0.00
% 2.15/1.29  Total                : 0.55
% 2.15/1.29  Index Insertion      : 0.00
% 2.15/1.29  Index Deletion       : 0.00
% 2.15/1.29  Index Matching       : 0.00
% 2.15/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
