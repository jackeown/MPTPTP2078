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
% DateTime   : Thu Dec  3 10:01:24 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   57 (  98 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 117 expanded)
%              Number of equality atoms :   43 (  88 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_56,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_34,plain,(
    ! [A_38] : k1_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_33] : v1_relat_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [A_45] :
      ( k1_relat_1(A_45) != k1_xboole_0
      | k1_xboole_0 = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_109,plain,(
    ! [A_33] :
      ( k1_relat_1(k6_relat_1(A_33)) != k1_xboole_0
      | k6_relat_1(A_33) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_128,plain,(
    ! [A_48] :
      ( k1_xboole_0 != A_48
      | k6_relat_1(A_48) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_109])).

tff(c_139,plain,(
    ! [A_48] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_20])).

tff(c_147,plain,(
    ! [A_48] : k1_xboole_0 != A_48 ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_2])).

tff(c_154,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_4,plain,(
    ! [B_3,A_2] : k2_tarski(B_3,A_2) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [A_46,B_47] : k1_setfam_1(k2_tarski(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_184,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(B_53,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_112])).

tff(c_18,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_207,plain,(
    ! [B_54,A_55] : k3_xboole_0(B_54,A_55) = k3_xboole_0(A_55,B_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_18])).

tff(c_223,plain,(
    ! [A_55] : k3_xboole_0(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_2])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_371,plain,(
    ! [B_67,A_68] :
      ( k10_relat_1(B_67,k3_xboole_0(k2_relat_1(B_67),A_68)) = k10_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,(
    ! [A_33] :
      ( k1_xboole_0 != A_33
      | k6_relat_1(A_33) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_109])).

tff(c_36,plain,(
    ! [A_38] : k2_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_287,plain,(
    ! [A_57] :
      ( k10_relat_1(A_57,k2_relat_1(A_57)) = k1_relat_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_296,plain,(
    ! [A_38] :
      ( k10_relat_1(k6_relat_1(A_38),A_38) = k1_relat_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_287])).

tff(c_313,plain,(
    ! [A_58] : k10_relat_1(k6_relat_1(A_58),A_58) = A_58 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34,c_296])).

tff(c_322,plain,(
    ! [A_33] :
      ( k10_relat_1(k1_xboole_0,A_33) = A_33
      | k1_xboole_0 != A_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_313])).

tff(c_378,plain,(
    ! [A_68] :
      ( k3_xboole_0(k2_relat_1(k1_xboole_0),A_68) = k10_relat_1(k1_xboole_0,A_68)
      | k3_xboole_0(k2_relat_1(k1_xboole_0),A_68) != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_322])).

tff(c_406,plain,(
    ! [A_68] : k10_relat_1(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_223,c_26,c_223,c_26,c_378])).

tff(c_38,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:26:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.30  
% 2.36/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.31  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.36/1.31  
% 2.36/1.31  %Foreground sorts:
% 2.36/1.31  
% 2.36/1.31  
% 2.36/1.31  %Background operators:
% 2.36/1.31  
% 2.36/1.31  
% 2.36/1.31  %Foreground operators:
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.36/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.31  
% 2.36/1.32  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.36/1.32  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.36/1.32  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.36/1.32  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.36/1.32  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.36/1.32  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.36/1.32  tff(f_56, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.36/1.32  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.36/1.32  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.36/1.32  tff(f_71, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.36/1.32  tff(c_34, plain, (![A_38]: (k1_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.32  tff(c_20, plain, (![A_33]: (v1_relat_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.32  tff(c_106, plain, (![A_45]: (k1_relat_1(A_45)!=k1_xboole_0 | k1_xboole_0=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.36/1.32  tff(c_109, plain, (![A_33]: (k1_relat_1(k6_relat_1(A_33))!=k1_xboole_0 | k6_relat_1(A_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_106])).
% 2.36/1.32  tff(c_128, plain, (![A_48]: (k1_xboole_0!=A_48 | k6_relat_1(A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_109])).
% 2.36/1.32  tff(c_139, plain, (![A_48]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_128, c_20])).
% 2.36/1.32  tff(c_147, plain, (![A_48]: (k1_xboole_0!=A_48)), inference(splitLeft, [status(thm)], [c_139])).
% 2.36/1.32  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.36/1.32  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_2])).
% 2.36/1.32  tff(c_154, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_139])).
% 2.36/1.32  tff(c_4, plain, (![B_3, A_2]: (k2_tarski(B_3, A_2)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.32  tff(c_112, plain, (![A_46, B_47]: (k1_setfam_1(k2_tarski(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.32  tff(c_184, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(B_53, A_52))), inference(superposition, [status(thm), theory('equality')], [c_4, c_112])).
% 2.36/1.32  tff(c_18, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.32  tff(c_207, plain, (![B_54, A_55]: (k3_xboole_0(B_54, A_55)=k3_xboole_0(A_55, B_54))), inference(superposition, [status(thm), theory('equality')], [c_184, c_18])).
% 2.36/1.32  tff(c_223, plain, (![A_55]: (k3_xboole_0(k1_xboole_0, A_55)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_207, c_2])).
% 2.36/1.32  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.36/1.32  tff(c_371, plain, (![B_67, A_68]: (k10_relat_1(B_67, k3_xboole_0(k2_relat_1(B_67), A_68))=k10_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.32  tff(c_111, plain, (![A_33]: (k1_xboole_0!=A_33 | k6_relat_1(A_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_109])).
% 2.36/1.32  tff(c_36, plain, (![A_38]: (k2_relat_1(k6_relat_1(A_38))=A_38)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.32  tff(c_287, plain, (![A_57]: (k10_relat_1(A_57, k2_relat_1(A_57))=k1_relat_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.32  tff(c_296, plain, (![A_38]: (k10_relat_1(k6_relat_1(A_38), A_38)=k1_relat_1(k6_relat_1(A_38)) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_287])).
% 2.36/1.32  tff(c_313, plain, (![A_58]: (k10_relat_1(k6_relat_1(A_58), A_58)=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_34, c_296])).
% 2.36/1.32  tff(c_322, plain, (![A_33]: (k10_relat_1(k1_xboole_0, A_33)=A_33 | k1_xboole_0!=A_33)), inference(superposition, [status(thm), theory('equality')], [c_111, c_313])).
% 2.36/1.32  tff(c_378, plain, (![A_68]: (k3_xboole_0(k2_relat_1(k1_xboole_0), A_68)=k10_relat_1(k1_xboole_0, A_68) | k3_xboole_0(k2_relat_1(k1_xboole_0), A_68)!=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_371, c_322])).
% 2.36/1.32  tff(c_406, plain, (![A_68]: (k10_relat_1(k1_xboole_0, A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_223, c_26, c_223, c_26, c_378])).
% 2.36/1.32  tff(c_38, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.36/1.32  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_406, c_38])).
% 2.36/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.32  
% 2.36/1.32  Inference rules
% 2.36/1.32  ----------------------
% 2.36/1.32  #Ref     : 0
% 2.36/1.32  #Sup     : 86
% 2.36/1.32  #Fact    : 0
% 2.36/1.32  #Define  : 0
% 2.36/1.32  #Split   : 2
% 2.36/1.32  #Chain   : 0
% 2.36/1.32  #Close   : 0
% 2.36/1.32  
% 2.36/1.32  Ordering : KBO
% 2.36/1.32  
% 2.36/1.32  Simplification rules
% 2.36/1.32  ----------------------
% 2.36/1.32  #Subsume      : 5
% 2.36/1.32  #Demod        : 45
% 2.36/1.32  #Tautology    : 71
% 2.36/1.32  #SimpNegUnit  : 5
% 2.36/1.32  #BackRed      : 4
% 2.36/1.32  
% 2.36/1.32  #Partial instantiations: 0
% 2.36/1.32  #Strategies tried      : 1
% 2.36/1.32  
% 2.36/1.32  Timing (in seconds)
% 2.36/1.32  ----------------------
% 2.36/1.32  Preprocessing        : 0.33
% 2.36/1.32  Parsing              : 0.18
% 2.36/1.32  CNF conversion       : 0.02
% 2.36/1.32  Main loop            : 0.19
% 2.36/1.32  Inferencing          : 0.07
% 2.36/1.32  Reduction            : 0.07
% 2.36/1.32  Demodulation         : 0.05
% 2.36/1.32  BG Simplification    : 0.01
% 2.36/1.32  Subsumption          : 0.02
% 2.36/1.32  Abstraction          : 0.01
% 2.36/1.32  MUC search           : 0.00
% 2.36/1.32  Cooper               : 0.00
% 2.36/1.32  Total                : 0.54
% 2.36/1.32  Index Insertion      : 0.00
% 2.36/1.32  Index Deletion       : 0.00
% 2.36/1.32  Index Matching       : 0.00
% 2.36/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
