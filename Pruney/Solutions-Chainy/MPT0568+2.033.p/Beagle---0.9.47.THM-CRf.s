%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:24 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   60 (  87 expanded)
%              Number of leaves         :   32 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 ( 101 expanded)
%              Number of equality atoms :   42 (  72 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_38,plain,(
    ! [A_41] : k1_relat_1(k6_relat_1(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_182,plain,(
    ! [A_52] :
      ( k1_relat_1(A_52) != k1_xboole_0
      | k1_xboole_0 = A_52
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_185,plain,(
    ! [A_36] :
      ( k1_relat_1(k6_relat_1(A_36)) != k1_xboole_0
      | k6_relat_1(A_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_182])).

tff(c_198,plain,(
    ! [A_55] :
      ( k1_xboole_0 != A_55
      | k6_relat_1(A_55) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_185])).

tff(c_209,plain,(
    ! [A_55] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_55 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_24])).

tff(c_217,plain,(
    ! [A_55] : k1_xboole_0 != A_55 ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_6])).

tff(c_224,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_187,plain,(
    ! [A_36] :
      ( k1_xboole_0 != A_36
      | k6_relat_1(A_36) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_185])).

tff(c_40,plain,(
    ! [A_41] : k2_relat_1(k6_relat_1(A_41)) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_245,plain,(
    ! [A_57] :
      ( k10_relat_1(A_57,k2_relat_1(A_57)) = k1_relat_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_254,plain,(
    ! [A_41] :
      ( k10_relat_1(k6_relat_1(A_41),A_41) = k1_relat_1(k6_relat_1(A_41))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_245])).

tff(c_268,plain,(
    ! [A_58] : k10_relat_1(k6_relat_1(A_58),A_58) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_38,c_254])).

tff(c_280,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_268])).

tff(c_306,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_86,plain,(
    ! [B_47,A_48] : k5_xboole_0(B_47,A_48) = k5_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [A_48] : k5_xboole_0(k1_xboole_0,A_48) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8])).

tff(c_313,plain,(
    ! [B_61] : k4_xboole_0(k1_xboole_0,B_61) = k3_xboole_0(k1_xboole_0,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_102])).

tff(c_322,plain,(
    ! [B_61] : k3_xboole_0(k1_xboole_0,B_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_313])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_347,plain,(
    ! [B_66,A_67] :
      ( k10_relat_1(B_66,k3_xboole_0(k2_relat_1(B_66),A_67)) = k10_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_367,plain,(
    ! [A_67] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_67)) = k10_relat_1(k1_xboole_0,A_67)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_347])).

tff(c_377,plain,(
    ! [A_67] : k10_relat_1(k1_xboole_0,A_67) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_280,c_322,c_367])).

tff(c_42,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:55:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.27  
% 2.30/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.28  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.30/1.28  
% 2.30/1.28  %Foreground sorts:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Background operators:
% 2.30/1.28  
% 2.30/1.28  
% 2.30/1.28  %Foreground operators:
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.30/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.30/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.30/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.30/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.30/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.30/1.28  
% 2.30/1.29  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.30/1.29  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.30/1.29  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.30/1.29  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.30/1.29  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.30/1.29  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.30/1.29  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.30/1.29  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.30/1.29  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.30/1.29  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.30/1.29  tff(f_75, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.30/1.29  tff(c_38, plain, (![A_41]: (k1_relat_1(k6_relat_1(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.29  tff(c_24, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.30/1.29  tff(c_182, plain, (![A_52]: (k1_relat_1(A_52)!=k1_xboole_0 | k1_xboole_0=A_52 | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.30/1.29  tff(c_185, plain, (![A_36]: (k1_relat_1(k6_relat_1(A_36))!=k1_xboole_0 | k6_relat_1(A_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_182])).
% 2.30/1.29  tff(c_198, plain, (![A_55]: (k1_xboole_0!=A_55 | k6_relat_1(A_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_185])).
% 2.30/1.29  tff(c_209, plain, (![A_55]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_55)), inference(superposition, [status(thm), theory('equality')], [c_198, c_24])).
% 2.30/1.29  tff(c_217, plain, (![A_55]: (k1_xboole_0!=A_55)), inference(splitLeft, [status(thm)], [c_209])).
% 2.30/1.29  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.29  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_6])).
% 2.30/1.29  tff(c_224, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_209])).
% 2.30/1.29  tff(c_187, plain, (![A_36]: (k1_xboole_0!=A_36 | k6_relat_1(A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_185])).
% 2.30/1.29  tff(c_40, plain, (![A_41]: (k2_relat_1(k6_relat_1(A_41))=A_41)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.29  tff(c_245, plain, (![A_57]: (k10_relat_1(A_57, k2_relat_1(A_57))=k1_relat_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.30/1.29  tff(c_254, plain, (![A_41]: (k10_relat_1(k6_relat_1(A_41), A_41)=k1_relat_1(k6_relat_1(A_41)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_245])).
% 2.30/1.29  tff(c_268, plain, (![A_58]: (k10_relat_1(k6_relat_1(A_58), A_58)=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_38, c_254])).
% 2.30/1.29  tff(c_280, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_187, c_268])).
% 2.30/1.29  tff(c_306, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.29  tff(c_86, plain, (![B_47, A_48]: (k5_xboole_0(B_47, A_48)=k5_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.29  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.29  tff(c_102, plain, (![A_48]: (k5_xboole_0(k1_xboole_0, A_48)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_86, c_8])).
% 2.30/1.29  tff(c_313, plain, (![B_61]: (k4_xboole_0(k1_xboole_0, B_61)=k3_xboole_0(k1_xboole_0, B_61))), inference(superposition, [status(thm), theory('equality')], [c_306, c_102])).
% 2.30/1.29  tff(c_322, plain, (![B_61]: (k3_xboole_0(k1_xboole_0, B_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_313])).
% 2.30/1.29  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.30/1.29  tff(c_347, plain, (![B_66, A_67]: (k10_relat_1(B_66, k3_xboole_0(k2_relat_1(B_66), A_67))=k10_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.30/1.29  tff(c_367, plain, (![A_67]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_67))=k10_relat_1(k1_xboole_0, A_67) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_347])).
% 2.30/1.29  tff(c_377, plain, (![A_67]: (k10_relat_1(k1_xboole_0, A_67)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_224, c_280, c_322, c_367])).
% 2.30/1.29  tff(c_42, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.30/1.29  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_377, c_42])).
% 2.30/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.29  
% 2.30/1.29  Inference rules
% 2.30/1.29  ----------------------
% 2.30/1.29  #Ref     : 0
% 2.30/1.29  #Sup     : 74
% 2.30/1.29  #Fact    : 0
% 2.30/1.29  #Define  : 0
% 2.30/1.29  #Split   : 2
% 2.30/1.29  #Chain   : 0
% 2.30/1.29  #Close   : 0
% 2.30/1.29  
% 2.30/1.29  Ordering : KBO
% 2.30/1.29  
% 2.30/1.29  Simplification rules
% 2.30/1.29  ----------------------
% 2.30/1.29  #Subsume      : 4
% 2.30/1.29  #Demod        : 47
% 2.30/1.29  #Tautology    : 63
% 2.30/1.29  #SimpNegUnit  : 5
% 2.30/1.29  #BackRed      : 4
% 2.30/1.29  
% 2.30/1.29  #Partial instantiations: 0
% 2.30/1.29  #Strategies tried      : 1
% 2.30/1.29  
% 2.30/1.29  Timing (in seconds)
% 2.30/1.29  ----------------------
% 2.30/1.29  Preprocessing        : 0.33
% 2.30/1.29  Parsing              : 0.17
% 2.30/1.29  CNF conversion       : 0.02
% 2.30/1.29  Main loop            : 0.20
% 2.30/1.29  Inferencing          : 0.07
% 2.30/1.29  Reduction            : 0.07
% 2.30/1.29  Demodulation         : 0.05
% 2.30/1.29  BG Simplification    : 0.02
% 2.30/1.29  Subsumption          : 0.02
% 2.30/1.29  Abstraction          : 0.01
% 2.30/1.29  MUC search           : 0.00
% 2.30/1.29  Cooper               : 0.00
% 2.30/1.29  Total                : 0.55
% 2.30/1.29  Index Insertion      : 0.00
% 2.30/1.29  Index Deletion       : 0.00
% 2.30/1.29  Index Matching       : 0.00
% 2.30/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
