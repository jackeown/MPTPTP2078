%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:32 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 145 expanded)
%              Number of equality atoms :   53 ( 108 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_44,plain,(
    ! [A_45] : k1_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    ! [A_40] : v1_relat_1(k6_relat_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_100,plain,(
    ! [A_53] :
      ( k1_relat_1(A_53) != k1_xboole_0
      | k1_xboole_0 = A_53
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_103,plain,(
    ! [A_40] :
      ( k1_relat_1(k6_relat_1(A_40)) != k1_xboole_0
      | k6_relat_1(A_40) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_100])).

tff(c_107,plain,(
    ! [A_54] :
      ( k1_xboole_0 != A_54
      | k6_relat_1(A_54) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_118,plain,(
    ! [A_54] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_54 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_30])).

tff(c_126,plain,(
    ! [A_54] : k1_xboole_0 != A_54 ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_10])).

tff(c_134,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(A_57,B_58) = B_58
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    ! [A_6] : k2_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_12,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_219,plain,(
    ! [A_66,B_67] : k5_xboole_0(A_66,k3_xboole_0(A_66,B_67)) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_228,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_219])).

tff(c_232,plain,(
    ! [A_68] : k4_xboole_0(A_68,k1_xboole_0) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_228])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_238,plain,(
    ! [A_68] : k5_xboole_0(k1_xboole_0,A_68) = k2_xboole_0(k1_xboole_0,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_14])).

tff(c_255,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,A_69) = A_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_238])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_262,plain,(
    ! [B_2] : k4_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_2])).

tff(c_287,plain,(
    ! [B_2] : k3_xboole_0(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_262])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_385,plain,(
    ! [B_77,A_78] :
      ( k10_relat_1(B_77,k3_xboole_0(k2_relat_1(B_77),A_78)) = k10_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    ! [A_40] :
      ( k1_xboole_0 != A_40
      | k6_relat_1(A_40) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_46,plain,(
    ! [A_45] : k2_relat_1(k6_relat_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_294,plain,(
    ! [A_70] :
      ( k10_relat_1(A_70,k2_relat_1(A_70)) = k1_relat_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_303,plain,(
    ! [A_45] :
      ( k10_relat_1(k6_relat_1(A_45),A_45) = k1_relat_1(k6_relat_1(A_45))
      | ~ v1_relat_1(k6_relat_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_294])).

tff(c_346,plain,(
    ! [A_75] : k10_relat_1(k6_relat_1(A_75),A_75) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44,c_303])).

tff(c_355,plain,(
    ! [A_40] :
      ( k10_relat_1(k1_xboole_0,A_40) = A_40
      | k1_xboole_0 != A_40 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_346])).

tff(c_392,plain,(
    ! [A_78] :
      ( k3_xboole_0(k2_relat_1(k1_xboole_0),A_78) = k10_relat_1(k1_xboole_0,A_78)
      | k3_xboole_0(k2_relat_1(k1_xboole_0),A_78) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_355])).

tff(c_412,plain,(
    ! [A_78] : k10_relat_1(k1_xboole_0,A_78) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_287,c_36,c_287,c_36,c_392])).

tff(c_48,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.29  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.12/1.29  
% 2.12/1.29  %Foreground sorts:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Background operators:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Foreground operators:
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.12/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.29  
% 2.12/1.30  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.12/1.30  tff(f_57, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.12/1.30  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.12/1.30  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.12/1.30  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.12/1.30  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.12/1.30  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.12/1.30  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.30  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.12/1.30  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.12/1.30  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.30  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.12/1.30  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.12/1.30  tff(f_83, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.12/1.30  tff(c_44, plain, (![A_45]: (k1_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.12/1.30  tff(c_30, plain, (![A_40]: (v1_relat_1(k6_relat_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.12/1.30  tff(c_100, plain, (![A_53]: (k1_relat_1(A_53)!=k1_xboole_0 | k1_xboole_0=A_53 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.12/1.30  tff(c_103, plain, (![A_40]: (k1_relat_1(k6_relat_1(A_40))!=k1_xboole_0 | k6_relat_1(A_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_100])).
% 2.12/1.30  tff(c_107, plain, (![A_54]: (k1_xboole_0!=A_54 | k6_relat_1(A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_103])).
% 2.12/1.30  tff(c_118, plain, (![A_54]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_54)), inference(superposition, [status(thm), theory('equality')], [c_107, c_30])).
% 2.12/1.30  tff(c_126, plain, (![A_54]: (k1_xboole_0!=A_54)), inference(splitLeft, [status(thm)], [c_118])).
% 2.12/1.30  tff(c_10, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.30  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_10])).
% 2.12/1.30  tff(c_134, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_118])).
% 2.12/1.30  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.30  tff(c_151, plain, (![A_57, B_58]: (k2_xboole_0(A_57, B_58)=B_58 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.30  tff(c_155, plain, (![A_6]: (k2_xboole_0(k1_xboole_0, A_6)=A_6)), inference(resolution, [status(thm)], [c_8, c_151])).
% 2.12/1.30  tff(c_12, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.30  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.30  tff(c_219, plain, (![A_66, B_67]: (k5_xboole_0(A_66, k3_xboole_0(A_66, B_67))=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.30  tff(c_228, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_219])).
% 2.12/1.30  tff(c_232, plain, (![A_68]: (k4_xboole_0(A_68, k1_xboole_0)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_228])).
% 2.12/1.30  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.30  tff(c_238, plain, (![A_68]: (k5_xboole_0(k1_xboole_0, A_68)=k2_xboole_0(k1_xboole_0, A_68))), inference(superposition, [status(thm), theory('equality')], [c_232, c_14])).
% 2.12/1.30  tff(c_255, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, A_69)=A_69)), inference(demodulation, [status(thm), theory('equality')], [c_155, c_238])).
% 2.12/1.30  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.30  tff(c_262, plain, (![B_2]: (k4_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_255, c_2])).
% 2.12/1.30  tff(c_287, plain, (![B_2]: (k3_xboole_0(k1_xboole_0, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_262])).
% 2.12/1.30  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.30  tff(c_385, plain, (![B_77, A_78]: (k10_relat_1(B_77, k3_xboole_0(k2_relat_1(B_77), A_78))=k10_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.12/1.30  tff(c_105, plain, (![A_40]: (k1_xboole_0!=A_40 | k6_relat_1(A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_103])).
% 2.12/1.30  tff(c_46, plain, (![A_45]: (k2_relat_1(k6_relat_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.12/1.30  tff(c_294, plain, (![A_70]: (k10_relat_1(A_70, k2_relat_1(A_70))=k1_relat_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.30  tff(c_303, plain, (![A_45]: (k10_relat_1(k6_relat_1(A_45), A_45)=k1_relat_1(k6_relat_1(A_45)) | ~v1_relat_1(k6_relat_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_294])).
% 2.12/1.30  tff(c_346, plain, (![A_75]: (k10_relat_1(k6_relat_1(A_75), A_75)=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44, c_303])).
% 2.12/1.30  tff(c_355, plain, (![A_40]: (k10_relat_1(k1_xboole_0, A_40)=A_40 | k1_xboole_0!=A_40)), inference(superposition, [status(thm), theory('equality')], [c_105, c_346])).
% 2.12/1.30  tff(c_392, plain, (![A_78]: (k3_xboole_0(k2_relat_1(k1_xboole_0), A_78)=k10_relat_1(k1_xboole_0, A_78) | k3_xboole_0(k2_relat_1(k1_xboole_0), A_78)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_385, c_355])).
% 2.12/1.30  tff(c_412, plain, (![A_78]: (k10_relat_1(k1_xboole_0, A_78)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_287, c_36, c_287, c_36, c_392])).
% 2.12/1.30  tff(c_48, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.12/1.30  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_412, c_48])).
% 2.12/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  Inference rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Ref     : 0
% 2.12/1.30  #Sup     : 83
% 2.12/1.30  #Fact    : 0
% 2.12/1.30  #Define  : 0
% 2.12/1.30  #Split   : 2
% 2.12/1.30  #Chain   : 0
% 2.12/1.30  #Close   : 0
% 2.12/1.30  
% 2.12/1.30  Ordering : KBO
% 2.12/1.30  
% 2.12/1.30  Simplification rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Subsume      : 4
% 2.12/1.30  #Demod        : 47
% 2.12/1.30  #Tautology    : 69
% 2.12/1.30  #SimpNegUnit  : 6
% 2.12/1.30  #BackRed      : 5
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.31  #Strategies tried      : 1
% 2.12/1.31  
% 2.12/1.31  Timing (in seconds)
% 2.12/1.31  ----------------------
% 2.12/1.31  Preprocessing        : 0.31
% 2.12/1.31  Parsing              : 0.17
% 2.12/1.31  CNF conversion       : 0.02
% 2.12/1.31  Main loop            : 0.19
% 2.12/1.31  Inferencing          : 0.07
% 2.12/1.31  Reduction            : 0.06
% 2.12/1.31  Demodulation         : 0.05
% 2.12/1.31  BG Simplification    : 0.01
% 2.12/1.31  Subsumption          : 0.02
% 2.12/1.31  Abstraction          : 0.01
% 2.12/1.31  MUC search           : 0.00
% 2.12/1.31  Cooper               : 0.00
% 2.12/1.31  Total                : 0.53
% 2.12/1.31  Index Insertion      : 0.00
% 2.12/1.31  Index Deletion       : 0.00
% 2.12/1.31  Index Matching       : 0.00
% 2.12/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
