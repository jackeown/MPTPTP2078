%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:37 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [B_27,A_28] :
      ( k5_relat_1(B_27,k6_relat_1(A_28)) = B_27
      | ~ r1_tarski(k2_relat_1(B_27),A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [A_9,A_28] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_28)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_28)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_76])).

tff(c_82,plain,(
    ! [A_29,A_30] :
      ( k5_relat_1(k6_relat_1(A_29),k6_relat_1(A_30)) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_79])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k5_relat_1(k6_relat_1(A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [A_30,A_29] :
      ( k7_relat_1(k6_relat_1(A_30),A_29) = k6_relat_1(A_29)
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ r1_tarski(A_29,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_16])).

tff(c_101,plain,(
    ! [A_30,A_29] :
      ( k7_relat_1(k6_relat_1(A_30),A_29) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_88])).

tff(c_118,plain,(
    ! [B_33,A_34] :
      ( k7_relat_1(B_33,k3_xboole_0(k1_relat_1(B_33),A_34)) = k7_relat_1(B_33,A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [A_30,A_34] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_30)),A_34)) = k7_relat_1(k6_relat_1(A_30),A_34)
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_30)),A_34),A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_118])).

tff(c_141,plain,(
    ! [A_30,A_34] : k7_relat_1(k6_relat_1(A_30),A_34) = k6_relat_1(k3_xboole_0(A_30,A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10,c_18,c_10,c_132])).

tff(c_62,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = k7_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_68,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_22])).

tff(c_74,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.79/1.15  
% 1.79/1.15  %Foreground sorts:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Background operators:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Foreground operators:
% 1.79/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.79/1.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.79/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.79/1.15  
% 1.86/1.16  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.86/1.16  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.86/1.16  tff(f_53, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.86/1.16  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.86/1.16  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.86/1.16  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 1.86/1.16  tff(f_56, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.86/1.16  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.16  tff(c_10, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.16  tff(c_18, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.86/1.16  tff(c_12, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.16  tff(c_76, plain, (![B_27, A_28]: (k5_relat_1(B_27, k6_relat_1(A_28))=B_27 | ~r1_tarski(k2_relat_1(B_27), A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.86/1.16  tff(c_79, plain, (![A_9, A_28]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_28))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_28) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_76])).
% 1.86/1.16  tff(c_82, plain, (![A_29, A_30]: (k5_relat_1(k6_relat_1(A_29), k6_relat_1(A_30))=k6_relat_1(A_29) | ~r1_tarski(A_29, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_79])).
% 1.86/1.16  tff(c_16, plain, (![A_12, B_13]: (k5_relat_1(k6_relat_1(A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.86/1.16  tff(c_88, plain, (![A_30, A_29]: (k7_relat_1(k6_relat_1(A_30), A_29)=k6_relat_1(A_29) | ~v1_relat_1(k6_relat_1(A_30)) | ~r1_tarski(A_29, A_30))), inference(superposition, [status(thm), theory('equality')], [c_82, c_16])).
% 1.86/1.16  tff(c_101, plain, (![A_30, A_29]: (k7_relat_1(k6_relat_1(A_30), A_29)=k6_relat_1(A_29) | ~r1_tarski(A_29, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_88])).
% 1.86/1.16  tff(c_118, plain, (![B_33, A_34]: (k7_relat_1(B_33, k3_xboole_0(k1_relat_1(B_33), A_34))=k7_relat_1(B_33, A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.16  tff(c_132, plain, (![A_30, A_34]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_30)), A_34))=k7_relat_1(k6_relat_1(A_30), A_34) | ~v1_relat_1(k6_relat_1(A_30)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_30)), A_34), A_30))), inference(superposition, [status(thm), theory('equality')], [c_101, c_118])).
% 1.86/1.16  tff(c_141, plain, (![A_30, A_34]: (k7_relat_1(k6_relat_1(A_30), A_34)=k6_relat_1(k3_xboole_0(A_30, A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10, c_18, c_10, c_132])).
% 1.86/1.16  tff(c_62, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=k7_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.86/1.16  tff(c_22, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.16  tff(c_68, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_22])).
% 1.86/1.16  tff(c_74, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_68])).
% 1.86/1.16  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_74])).
% 1.86/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  Inference rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Ref     : 0
% 1.86/1.16  #Sup     : 25
% 1.86/1.16  #Fact    : 0
% 1.86/1.16  #Define  : 0
% 1.86/1.16  #Split   : 1
% 1.86/1.16  #Chain   : 0
% 1.86/1.16  #Close   : 0
% 1.86/1.16  
% 1.86/1.16  Ordering : KBO
% 1.86/1.16  
% 1.86/1.16  Simplification rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Subsume      : 1
% 1.86/1.16  #Demod        : 15
% 1.86/1.16  #Tautology    : 16
% 1.86/1.16  #SimpNegUnit  : 0
% 1.86/1.16  #BackRed      : 2
% 1.86/1.16  
% 1.86/1.16  #Partial instantiations: 0
% 1.86/1.16  #Strategies tried      : 1
% 1.86/1.16  
% 1.86/1.16  Timing (in seconds)
% 1.86/1.16  ----------------------
% 1.86/1.16  Preprocessing        : 0.28
% 1.86/1.16  Parsing              : 0.15
% 1.86/1.16  CNF conversion       : 0.01
% 1.86/1.16  Main loop            : 0.12
% 1.86/1.16  Inferencing          : 0.05
% 1.86/1.16  Reduction            : 0.04
% 1.86/1.17  Demodulation         : 0.03
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.01
% 1.86/1.17  Abstraction          : 0.01
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.43
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.17  Index Matching       : 0.00
% 1.86/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
