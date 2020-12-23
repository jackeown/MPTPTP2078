%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:31 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  74 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_38,B_39,C_40] :
      ( r1_tarski(A_38,B_39)
      | ~ r1_tarski(A_38,k3_xboole_0(B_39,C_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [B_39,C_40] : r1_tarski(k3_xboole_0(B_39,C_40),B_39) ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_26,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_140,plain,(
    ! [B_53,A_54] :
      ( k5_relat_1(B_53,k6_relat_1(A_54)) = k8_relat_1(A_54,B_53)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),B_25) = k7_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_147,plain,(
    ! [A_54,A_24] :
      ( k8_relat_1(A_54,k6_relat_1(A_24)) = k7_relat_1(k6_relat_1(A_54),A_24)
      | ~ v1_relat_1(k6_relat_1(A_54))
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_30])).

tff(c_160,plain,(
    ! [A_54,A_24] : k8_relat_1(A_54,k6_relat_1(A_24)) = k7_relat_1(k6_relat_1(A_54),A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_147])).

tff(c_28,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_176,plain,(
    ! [A_57,B_58] :
      ( k8_relat_1(A_57,B_58) = B_58
      | ~ r1_tarski(k2_relat_1(B_58),A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_182,plain,(
    ! [A_57,A_23] :
      ( k8_relat_1(A_57,k6_relat_1(A_23)) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_57)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_176])).

tff(c_262,plain,(
    ! [A_64,A_65] :
      ( k7_relat_1(k6_relat_1(A_64),A_65) = k6_relat_1(A_65)
      | ~ r1_tarski(A_65,A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_160,c_182])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k7_relat_1(B_22,k3_xboole_0(k1_relat_1(B_22),A_21)) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_269,plain,(
    ! [A_64,A_21] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_64)),A_21)) = k7_relat_1(k6_relat_1(A_64),A_21)
      | ~ v1_relat_1(k6_relat_1(A_64))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_64)),A_21),A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_24])).

tff(c_292,plain,(
    ! [A_64,A_21] : k7_relat_1(k6_relat_1(A_64),A_21) = k6_relat_1(k3_xboole_0(A_64,A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_26,c_32,c_26,c_269])).

tff(c_126,plain,(
    ! [A_51,B_52] :
      ( k5_relat_1(k6_relat_1(A_51),B_52) = k7_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_132,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_36])).

tff(c_138,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_132])).

tff(c_308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.15/1.31  
% 2.15/1.31  %Foreground sorts:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Background operators:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Foreground operators:
% 2.15/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.15/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.15/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.15/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.15/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.15/1.31  
% 2.15/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.15/1.32  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.15/1.32  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.15/1.32  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.15/1.32  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.15/1.32  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.15/1.32  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.15/1.32  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 2.15/1.32  tff(f_78, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.15/1.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.32  tff(c_84, plain, (![A_38, B_39, C_40]: (r1_tarski(A_38, B_39) | ~r1_tarski(A_38, k3_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.32  tff(c_89, plain, (![B_39, C_40]: (r1_tarski(k3_xboole_0(B_39, C_40), B_39))), inference(resolution, [status(thm)], [c_6, c_84])).
% 2.15/1.32  tff(c_26, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.32  tff(c_32, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.15/1.32  tff(c_140, plain, (![B_53, A_54]: (k5_relat_1(B_53, k6_relat_1(A_54))=k8_relat_1(A_54, B_53) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.32  tff(c_30, plain, (![A_24, B_25]: (k5_relat_1(k6_relat_1(A_24), B_25)=k7_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.32  tff(c_147, plain, (![A_54, A_24]: (k8_relat_1(A_54, k6_relat_1(A_24))=k7_relat_1(k6_relat_1(A_54), A_24) | ~v1_relat_1(k6_relat_1(A_54)) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_30])).
% 2.15/1.32  tff(c_160, plain, (![A_54, A_24]: (k8_relat_1(A_54, k6_relat_1(A_24))=k7_relat_1(k6_relat_1(A_54), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_147])).
% 2.15/1.32  tff(c_28, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.32  tff(c_176, plain, (![A_57, B_58]: (k8_relat_1(A_57, B_58)=B_58 | ~r1_tarski(k2_relat_1(B_58), A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.32  tff(c_182, plain, (![A_57, A_23]: (k8_relat_1(A_57, k6_relat_1(A_23))=k6_relat_1(A_23) | ~r1_tarski(A_23, A_57) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_176])).
% 2.15/1.32  tff(c_262, plain, (![A_64, A_65]: (k7_relat_1(k6_relat_1(A_64), A_65)=k6_relat_1(A_65) | ~r1_tarski(A_65, A_64))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_160, c_182])).
% 2.15/1.32  tff(c_24, plain, (![B_22, A_21]: (k7_relat_1(B_22, k3_xboole_0(k1_relat_1(B_22), A_21))=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.32  tff(c_269, plain, (![A_64, A_21]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_64)), A_21))=k7_relat_1(k6_relat_1(A_64), A_21) | ~v1_relat_1(k6_relat_1(A_64)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_64)), A_21), A_64))), inference(superposition, [status(thm), theory('equality')], [c_262, c_24])).
% 2.15/1.32  tff(c_292, plain, (![A_64, A_21]: (k7_relat_1(k6_relat_1(A_64), A_21)=k6_relat_1(k3_xboole_0(A_64, A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_26, c_32, c_26, c_269])).
% 2.15/1.32  tff(c_126, plain, (![A_51, B_52]: (k5_relat_1(k6_relat_1(A_51), B_52)=k7_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.32  tff(c_36, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.15/1.32  tff(c_132, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_36])).
% 2.15/1.32  tff(c_138, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_132])).
% 2.15/1.32  tff(c_308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_292, c_138])).
% 2.15/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.32  
% 2.15/1.32  Inference rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Ref     : 0
% 2.15/1.32  #Sup     : 54
% 2.15/1.32  #Fact    : 0
% 2.15/1.32  #Define  : 0
% 2.15/1.32  #Split   : 0
% 2.15/1.32  #Chain   : 0
% 2.15/1.32  #Close   : 0
% 2.15/1.32  
% 2.15/1.32  Ordering : KBO
% 2.15/1.32  
% 2.15/1.32  Simplification rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Subsume      : 1
% 2.15/1.32  #Demod        : 38
% 2.15/1.32  #Tautology    : 35
% 2.15/1.32  #SimpNegUnit  : 0
% 2.15/1.32  #BackRed      : 3
% 2.15/1.32  
% 2.15/1.32  #Partial instantiations: 0
% 2.15/1.32  #Strategies tried      : 1
% 2.15/1.32  
% 2.15/1.32  Timing (in seconds)
% 2.15/1.32  ----------------------
% 2.15/1.32  Preprocessing        : 0.32
% 2.15/1.32  Parsing              : 0.18
% 2.15/1.32  CNF conversion       : 0.02
% 2.15/1.32  Main loop            : 0.17
% 2.15/1.32  Inferencing          : 0.06
% 2.15/1.32  Reduction            : 0.06
% 2.15/1.32  Demodulation         : 0.04
% 2.15/1.32  BG Simplification    : 0.01
% 2.15/1.32  Subsumption          : 0.02
% 2.15/1.32  Abstraction          : 0.01
% 2.15/1.32  MUC search           : 0.00
% 2.15/1.32  Cooper               : 0.00
% 2.15/1.32  Total                : 0.51
% 2.15/1.32  Index Insertion      : 0.00
% 2.15/1.32  Index Deletion       : 0.00
% 2.15/1.32  Index Matching       : 0.00
% 2.15/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
