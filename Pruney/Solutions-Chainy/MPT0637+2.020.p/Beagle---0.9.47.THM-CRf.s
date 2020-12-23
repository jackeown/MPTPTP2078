%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:26 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  84 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_34] : v1_relat_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k6_relat_1(k2_relat_1(A_31))) = A_31
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_222,plain,(
    ! [A_57,B_58] :
      ( k5_relat_1(k6_relat_1(A_57),B_58) = k7_relat_1(B_58,A_57)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_249,plain,(
    ! [A_57] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_57))),A_57) = k6_relat_1(A_57)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_57))))
      | ~ v1_relat_1(k6_relat_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_222])).

tff(c_263,plain,(
    ! [A_57] : k7_relat_1(k6_relat_1(A_57),A_57) = k6_relat_1(A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_26,c_249])).

tff(c_551,plain,(
    ! [C_85,A_86,B_87] :
      ( k7_relat_1(k7_relat_1(C_85,A_86),B_87) = k7_relat_1(C_85,k3_xboole_0(A_86,B_87))
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_572,plain,(
    ! [A_57,B_87] :
      ( k7_relat_1(k6_relat_1(A_57),k3_xboole_0(A_57,B_87)) = k7_relat_1(k6_relat_1(A_57),B_87)
      | ~ v1_relat_1(k6_relat_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_551])).

tff(c_2109,plain,(
    ! [A_130,B_131] : k7_relat_1(k6_relat_1(A_130),k3_xboole_0(A_130,B_131)) = k7_relat_1(k6_relat_1(A_130),B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_572])).

tff(c_282,plain,(
    ! [B_62,A_63] :
      ( k5_relat_1(B_62,k6_relat_1(A_63)) = k8_relat_1(A_63,B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [A_32,B_33] :
      ( k5_relat_1(k6_relat_1(A_32),B_33) = k7_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_289,plain,(
    ! [A_63,A_32] :
      ( k8_relat_1(A_63,k6_relat_1(A_32)) = k7_relat_1(k6_relat_1(A_63),A_32)
      | ~ v1_relat_1(k6_relat_1(A_63))
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_30])).

tff(c_319,plain,(
    ! [A_63,A_32] : k8_relat_1(A_63,k6_relat_1(A_32)) = k7_relat_1(k6_relat_1(A_63),A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32,c_289])).

tff(c_414,plain,(
    ! [A_75,B_76] :
      ( k8_relat_1(A_75,B_76) = B_76
      | ~ r1_tarski(k2_relat_1(B_76),A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_417,plain,(
    ! [A_75,A_30] :
      ( k8_relat_1(A_75,k6_relat_1(A_30)) = k6_relat_1(A_30)
      | ~ r1_tarski(A_30,A_75)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_414])).

tff(c_419,plain,(
    ! [A_75,A_30] :
      ( k7_relat_1(k6_relat_1(A_75),A_30) = k6_relat_1(A_30)
      | ~ r1_tarski(A_30,A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_319,c_417])).

tff(c_2121,plain,(
    ! [A_130,B_131] :
      ( k7_relat_1(k6_relat_1(A_130),B_131) = k6_relat_1(k3_xboole_0(A_130,B_131))
      | ~ r1_tarski(k3_xboole_0(A_130,B_131),A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2109,c_419])).

tff(c_2178,plain,(
    ! [A_130,B_131] : k7_relat_1(k6_relat_1(A_130),B_131) = k6_relat_1(k3_xboole_0(A_130,B_131)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2121])).

tff(c_36,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_239,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_36])).

tff(c_258,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_239])).

tff(c_2200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2178,c_258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.61  
% 3.55/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.61  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.55/1.61  
% 3.55/1.61  %Foreground sorts:
% 3.55/1.61  
% 3.55/1.61  
% 3.55/1.61  %Background operators:
% 3.55/1.61  
% 3.55/1.61  
% 3.55/1.61  %Foreground operators:
% 3.55/1.61  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.55/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.55/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.55/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.55/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.55/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.55/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.61  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.55/1.61  
% 3.55/1.62  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.55/1.62  tff(f_85, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.55/1.62  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.55/1.62  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.55/1.62  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.55/1.62  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 3.55/1.62  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 3.55/1.62  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 3.55/1.62  tff(f_88, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.55/1.62  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.55/1.62  tff(c_32, plain, (![A_34]: (v1_relat_1(k6_relat_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.55/1.62  tff(c_26, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.55/1.62  tff(c_28, plain, (![A_31]: (k5_relat_1(A_31, k6_relat_1(k2_relat_1(A_31)))=A_31 | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.55/1.62  tff(c_222, plain, (![A_57, B_58]: (k5_relat_1(k6_relat_1(A_57), B_58)=k7_relat_1(B_58, A_57) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.55/1.62  tff(c_249, plain, (![A_57]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_57))), A_57)=k6_relat_1(A_57) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_57)))) | ~v1_relat_1(k6_relat_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_222])).
% 3.55/1.62  tff(c_263, plain, (![A_57]: (k7_relat_1(k6_relat_1(A_57), A_57)=k6_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_26, c_249])).
% 3.55/1.62  tff(c_551, plain, (![C_85, A_86, B_87]: (k7_relat_1(k7_relat_1(C_85, A_86), B_87)=k7_relat_1(C_85, k3_xboole_0(A_86, B_87)) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.55/1.62  tff(c_572, plain, (![A_57, B_87]: (k7_relat_1(k6_relat_1(A_57), k3_xboole_0(A_57, B_87))=k7_relat_1(k6_relat_1(A_57), B_87) | ~v1_relat_1(k6_relat_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_263, c_551])).
% 3.55/1.62  tff(c_2109, plain, (![A_130, B_131]: (k7_relat_1(k6_relat_1(A_130), k3_xboole_0(A_130, B_131))=k7_relat_1(k6_relat_1(A_130), B_131))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_572])).
% 3.55/1.62  tff(c_282, plain, (![B_62, A_63]: (k5_relat_1(B_62, k6_relat_1(A_63))=k8_relat_1(A_63, B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.55/1.62  tff(c_30, plain, (![A_32, B_33]: (k5_relat_1(k6_relat_1(A_32), B_33)=k7_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.55/1.62  tff(c_289, plain, (![A_63, A_32]: (k8_relat_1(A_63, k6_relat_1(A_32))=k7_relat_1(k6_relat_1(A_63), A_32) | ~v1_relat_1(k6_relat_1(A_63)) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_30])).
% 3.55/1.62  tff(c_319, plain, (![A_63, A_32]: (k8_relat_1(A_63, k6_relat_1(A_32))=k7_relat_1(k6_relat_1(A_63), A_32))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_32, c_289])).
% 3.55/1.62  tff(c_414, plain, (![A_75, B_76]: (k8_relat_1(A_75, B_76)=B_76 | ~r1_tarski(k2_relat_1(B_76), A_75) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.62  tff(c_417, plain, (![A_75, A_30]: (k8_relat_1(A_75, k6_relat_1(A_30))=k6_relat_1(A_30) | ~r1_tarski(A_30, A_75) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_414])).
% 3.55/1.62  tff(c_419, plain, (![A_75, A_30]: (k7_relat_1(k6_relat_1(A_75), A_30)=k6_relat_1(A_30) | ~r1_tarski(A_30, A_75))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_319, c_417])).
% 3.55/1.62  tff(c_2121, plain, (![A_130, B_131]: (k7_relat_1(k6_relat_1(A_130), B_131)=k6_relat_1(k3_xboole_0(A_130, B_131)) | ~r1_tarski(k3_xboole_0(A_130, B_131), A_130))), inference(superposition, [status(thm), theory('equality')], [c_2109, c_419])).
% 3.55/1.62  tff(c_2178, plain, (![A_130, B_131]: (k7_relat_1(k6_relat_1(A_130), B_131)=k6_relat_1(k3_xboole_0(A_130, B_131)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2121])).
% 3.55/1.62  tff(c_36, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.55/1.62  tff(c_239, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_36])).
% 3.55/1.62  tff(c_258, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_239])).
% 3.55/1.62  tff(c_2200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2178, c_258])).
% 3.55/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.62  
% 3.55/1.62  Inference rules
% 3.55/1.62  ----------------------
% 3.55/1.62  #Ref     : 0
% 3.55/1.62  #Sup     : 502
% 3.55/1.62  #Fact    : 0
% 3.55/1.62  #Define  : 0
% 3.55/1.62  #Split   : 1
% 3.55/1.62  #Chain   : 0
% 3.55/1.62  #Close   : 0
% 3.55/1.62  
% 3.55/1.62  Ordering : KBO
% 3.55/1.62  
% 3.55/1.62  Simplification rules
% 3.55/1.62  ----------------------
% 3.55/1.62  #Subsume      : 36
% 3.55/1.62  #Demod        : 510
% 3.55/1.62  #Tautology    : 279
% 3.55/1.62  #SimpNegUnit  : 0
% 3.55/1.62  #BackRed      : 7
% 3.55/1.62  
% 3.55/1.62  #Partial instantiations: 0
% 3.55/1.62  #Strategies tried      : 1
% 3.55/1.62  
% 3.55/1.62  Timing (in seconds)
% 3.55/1.62  ----------------------
% 3.55/1.62  Preprocessing        : 0.30
% 3.55/1.62  Parsing              : 0.16
% 3.55/1.62  CNF conversion       : 0.02
% 3.55/1.62  Main loop            : 0.53
% 3.55/1.62  Inferencing          : 0.18
% 3.55/1.62  Reduction            : 0.22
% 3.55/1.62  Demodulation         : 0.18
% 3.55/1.62  BG Simplification    : 0.03
% 3.55/1.62  Subsumption          : 0.07
% 3.55/1.62  Abstraction          : 0.03
% 3.55/1.62  MUC search           : 0.00
% 3.55/1.62  Cooper               : 0.00
% 3.55/1.62  Total                : 0.86
% 3.55/1.62  Index Insertion      : 0.00
% 3.55/1.62  Index Deletion       : 0.00
% 3.55/1.62  Index Matching       : 0.00
% 3.55/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
