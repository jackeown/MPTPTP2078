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
% DateTime   : Thu Dec  3 10:00:35 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  69 expanded)
%              Number of equality atoms :   37 (  48 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_70,plain,(
    ! [A_39] :
      ( v1_relat_1(A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    ! [A_46] :
      ( k9_relat_1(A_46,k1_relat_1(A_46)) = k2_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_126])).

tff(c_139,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_34,c_135])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_157,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k4_xboole_0(B_50,A_49)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_166,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k2_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_192,plain,(
    ! [A_52] : k2_xboole_0(A_52,k1_xboole_0) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_198,plain,(
    ! [A_52] : k2_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_2])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_153,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_144])).

tff(c_170,plain,(
    ! [A_51] : k4_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_153])).

tff(c_14,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_176,plain,(
    ! [A_51] : k5_xboole_0(k1_xboole_0,A_51) = k2_xboole_0(k1_xboole_0,A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_14])).

tff(c_265,plain,(
    ! [A_57] : k5_xboole_0(k1_xboole_0,A_57) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_176])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_276,plain,(
    ! [B_4] : k4_xboole_0(k1_xboole_0,B_4) = k3_xboole_0(k1_xboole_0,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_6])).

tff(c_298,plain,(
    ! [B_4] : k3_xboole_0(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_276])).

tff(c_333,plain,(
    ! [B_63,A_64] :
      ( k9_relat_1(B_63,k3_xboole_0(k1_relat_1(B_63),A_64)) = k9_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_346,plain,(
    ! [A_64] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_64)) = k9_relat_1(k1_xboole_0,A_64)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_333])).

tff(c_351,plain,(
    ! [A_64] : k9_relat_1(k1_xboole_0,A_64) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_139,c_298,c_346])).

tff(c_38,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:30:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.21  %$ v1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.00/1.21  
% 2.00/1.21  %Foreground sorts:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Background operators:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Foreground operators:
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.00/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.00/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.00/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.00/1.21  
% 2.00/1.23  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.00/1.23  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.00/1.23  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.00/1.23  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.00/1.23  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.00/1.23  tff(f_36, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.00/1.23  tff(f_38, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.00/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.00/1.23  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.00/1.23  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.00/1.23  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 2.00/1.23  tff(f_68, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.00/1.23  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.00/1.23  tff(c_70, plain, (![A_39]: (v1_relat_1(A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.23  tff(c_74, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_70])).
% 2.00/1.23  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.23  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.00/1.23  tff(c_126, plain, (![A_46]: (k9_relat_1(A_46, k1_relat_1(A_46))=k2_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.00/1.23  tff(c_135, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_126])).
% 2.00/1.23  tff(c_139, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_34, c_135])).
% 2.00/1.23  tff(c_10, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.23  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.00/1.23  tff(c_157, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k4_xboole_0(B_50, A_49))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.00/1.23  tff(c_166, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k2_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_157])).
% 2.00/1.23  tff(c_192, plain, (![A_52]: (k2_xboole_0(A_52, k1_xboole_0)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_166])).
% 2.00/1.23  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.23  tff(c_198, plain, (![A_52]: (k2_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_192, c_2])).
% 2.00/1.23  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.00/1.23  tff(c_144, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.00/1.23  tff(c_153, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_144])).
% 2.00/1.23  tff(c_170, plain, (![A_51]: (k4_xboole_0(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_153])).
% 2.00/1.23  tff(c_14, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.00/1.23  tff(c_176, plain, (![A_51]: (k5_xboole_0(k1_xboole_0, A_51)=k2_xboole_0(k1_xboole_0, A_51))), inference(superposition, [status(thm), theory('equality')], [c_170, c_14])).
% 2.00/1.23  tff(c_265, plain, (![A_57]: (k5_xboole_0(k1_xboole_0, A_57)=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_176])).
% 2.00/1.23  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.00/1.23  tff(c_276, plain, (![B_4]: (k4_xboole_0(k1_xboole_0, B_4)=k3_xboole_0(k1_xboole_0, B_4))), inference(superposition, [status(thm), theory('equality')], [c_265, c_6])).
% 2.00/1.23  tff(c_298, plain, (![B_4]: (k3_xboole_0(k1_xboole_0, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_276])).
% 2.00/1.23  tff(c_333, plain, (![B_63, A_64]: (k9_relat_1(B_63, k3_xboole_0(k1_relat_1(B_63), A_64))=k9_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.00/1.23  tff(c_346, plain, (![A_64]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_64))=k9_relat_1(k1_xboole_0, A_64) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_333])).
% 2.00/1.23  tff(c_351, plain, (![A_64]: (k9_relat_1(k1_xboole_0, A_64)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_139, c_298, c_346])).
% 2.00/1.23  tff(c_38, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.00/1.23  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_351, c_38])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 74
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 0
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 0
% 2.00/1.23  #Demod        : 26
% 2.00/1.23  #Tautology    : 67
% 2.00/1.23  #SimpNegUnit  : 0
% 2.00/1.23  #BackRed      : 1
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.00/1.23  Preprocessing        : 0.31
% 2.00/1.23  Parsing              : 0.17
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.17
% 2.00/1.23  Inferencing          : 0.07
% 2.00/1.23  Reduction            : 0.06
% 2.00/1.23  Demodulation         : 0.04
% 2.00/1.23  BG Simplification    : 0.01
% 2.00/1.23  Subsumption          : 0.02
% 2.00/1.23  Abstraction          : 0.01
% 2.00/1.23  MUC search           : 0.00
% 2.00/1.23  Cooper               : 0.00
% 2.00/1.23  Total                : 0.51
% 2.00/1.23  Index Insertion      : 0.00
% 2.00/1.23  Index Deletion       : 0.00
% 2.00/1.23  Index Matching       : 0.00
% 2.00/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
