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
% DateTime   : Thu Dec  3 10:01:20 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  51 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_52,plain,(
    ! [A_41] :
      ( v1_relat_1(A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_171,plain,(
    ! [A_50] :
      ( k10_relat_1(A_50,k2_relat_1(A_50)) = k1_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_180,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_171])).

tff(c_184,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_34,c_180])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    ! [B_43,A_44] : k5_xboole_0(B_43,A_44) = k5_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [A_44] : k5_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_10])).

tff(c_196,plain,(
    ! [B_52] : k4_xboole_0(k1_xboole_0,B_52) = k3_xboole_0(k1_xboole_0,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_82])).

tff(c_205,plain,(
    ! [B_52] : k3_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_196])).

tff(c_229,plain,(
    ! [B_57,A_58] :
      ( k10_relat_1(B_57,k3_xboole_0(k2_relat_1(B_57),A_58)) = k10_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_238,plain,(
    ! [A_58] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_58)) = k10_relat_1(k1_xboole_0,A_58)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_229])).

tff(c_242,plain,(
    ! [A_58] : k10_relat_1(k1_xboole_0,A_58) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_184,c_205,c_238])).

tff(c_36,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.22  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.98/1.22  
% 1.98/1.22  %Foreground sorts:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Background operators:
% 1.98/1.22  
% 1.98/1.22  
% 1.98/1.22  %Foreground operators:
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.98/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.98/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.98/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.98/1.22  
% 2.07/1.23  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.07/1.23  tff(f_52, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.07/1.23  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.07/1.23  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.07/1.23  tff(f_32, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.07/1.23  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.07/1.23  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.07/1.23  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.07/1.23  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.07/1.23  tff(f_66, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.07/1.23  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.07/1.23  tff(c_52, plain, (![A_41]: (v1_relat_1(A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.07/1.23  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_52])).
% 2.07/1.23  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.07/1.23  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.07/1.23  tff(c_171, plain, (![A_50]: (k10_relat_1(A_50, k2_relat_1(A_50))=k1_relat_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.23  tff(c_180, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_171])).
% 2.07/1.23  tff(c_184, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_34, c_180])).
% 2.07/1.23  tff(c_8, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.23  tff(c_189, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.07/1.23  tff(c_66, plain, (![B_43, A_44]: (k5_xboole_0(B_43, A_44)=k5_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.23  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.07/1.23  tff(c_82, plain, (![A_44]: (k5_xboole_0(k1_xboole_0, A_44)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_66, c_10])).
% 2.07/1.23  tff(c_196, plain, (![B_52]: (k4_xboole_0(k1_xboole_0, B_52)=k3_xboole_0(k1_xboole_0, B_52))), inference(superposition, [status(thm), theory('equality')], [c_189, c_82])).
% 2.07/1.23  tff(c_205, plain, (![B_52]: (k3_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_196])).
% 2.07/1.23  tff(c_229, plain, (![B_57, A_58]: (k10_relat_1(B_57, k3_xboole_0(k2_relat_1(B_57), A_58))=k10_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.23  tff(c_238, plain, (![A_58]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_58))=k10_relat_1(k1_xboole_0, A_58) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_229])).
% 2.07/1.23  tff(c_242, plain, (![A_58]: (k10_relat_1(k1_xboole_0, A_58)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_184, c_205, c_238])).
% 2.07/1.23  tff(c_36, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.23  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_36])).
% 2.07/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.23  
% 2.07/1.23  Inference rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Ref     : 0
% 2.07/1.23  #Sup     : 50
% 2.07/1.23  #Fact    : 0
% 2.07/1.23  #Define  : 0
% 2.07/1.23  #Split   : 0
% 2.07/1.23  #Chain   : 0
% 2.07/1.23  #Close   : 0
% 2.07/1.23  
% 2.07/1.23  Ordering : KBO
% 2.07/1.23  
% 2.07/1.23  Simplification rules
% 2.07/1.23  ----------------------
% 2.07/1.23  #Subsume      : 0
% 2.07/1.23  #Demod        : 19
% 2.07/1.23  #Tautology    : 46
% 2.07/1.23  #SimpNegUnit  : 0
% 2.07/1.23  #BackRed      : 1
% 2.07/1.23  
% 2.07/1.23  #Partial instantiations: 0
% 2.07/1.23  #Strategies tried      : 1
% 2.07/1.23  
% 2.07/1.23  Timing (in seconds)
% 2.07/1.23  ----------------------
% 2.07/1.23  Preprocessing        : 0.31
% 2.07/1.23  Parsing              : 0.16
% 2.07/1.23  CNF conversion       : 0.02
% 2.07/1.23  Main loop            : 0.14
% 2.07/1.23  Inferencing          : 0.06
% 2.07/1.23  Reduction            : 0.05
% 2.07/1.23  Demodulation         : 0.04
% 2.07/1.23  BG Simplification    : 0.01
% 2.07/1.23  Subsumption          : 0.02
% 2.07/1.23  Abstraction          : 0.01
% 2.07/1.23  MUC search           : 0.00
% 2.07/1.23  Cooper               : 0.00
% 2.07/1.23  Total                : 0.47
% 2.07/1.23  Index Insertion      : 0.00
% 2.07/1.23  Index Deletion       : 0.00
% 2.07/1.23  Index Matching       : 0.00
% 2.07/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
