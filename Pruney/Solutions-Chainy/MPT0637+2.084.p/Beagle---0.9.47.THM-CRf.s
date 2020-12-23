%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:35 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   45 (  67 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  79 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_28,B_29] :
      ( k5_relat_1(k6_relat_1(A_28),B_29) = k7_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [A_8,A_28] :
      ( k8_relat_1(A_8,k6_relat_1(A_28)) = k7_relat_1(k6_relat_1(A_8),A_28)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_10])).

tff(c_95,plain,(
    ! [A_8,A_28] : k8_relat_1(A_8,k6_relat_1(A_28)) = k7_relat_1(k6_relat_1(A_8),A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_82])).

tff(c_18,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_112,plain,(
    ! [A_32,B_33] :
      ( k8_relat_1(A_32,B_33) = B_33
      | ~ r1_tarski(k2_relat_1(B_33),A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_32,A_14] :
      ( k8_relat_1(A_32,k6_relat_1(A_14)) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_32)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_112])).

tff(c_132,plain,(
    ! [A_36,A_37] :
      ( k7_relat_1(k6_relat_1(A_36),A_37) = k6_relat_1(A_37)
      | ~ r1_tarski(A_37,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_95,c_115])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,k3_xboole_0(k1_relat_1(B_13),A_12)) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_139,plain,(
    ! [A_36,A_12] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_36)),A_12)) = k7_relat_1(k6_relat_1(A_36),A_12)
      | ~ v1_relat_1(k6_relat_1(A_36))
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_36)),A_12),A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_14])).

tff(c_152,plain,(
    ! [A_36,A_12] : k7_relat_1(k6_relat_1(A_36),A_12) = k6_relat_1(k3_xboole_0(A_36,A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16,c_8,c_16,c_139])).

tff(c_61,plain,(
    ! [B_26,A_27] :
      ( k5_relat_1(B_26,k6_relat_1(A_27)) = k8_relat_1(A_27,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_67,plain,
    ( k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_22])).

tff(c_73,plain,(
    k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_101,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_73])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.64/1.14  
% 1.64/1.14  %Foreground sorts:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Background operators:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Foreground operators:
% 1.64/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.64/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.64/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.64/1.14  
% 1.64/1.15  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.64/1.15  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.64/1.15  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.64/1.15  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.64/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.64/1.15  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 1.64/1.15  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 1.64/1.15  tff(f_58, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.64/1.15  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.15  tff(c_16, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.64/1.15  tff(c_8, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.15  tff(c_75, plain, (![A_28, B_29]: (k5_relat_1(k6_relat_1(A_28), B_29)=k7_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.64/1.15  tff(c_10, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.15  tff(c_82, plain, (![A_8, A_28]: (k8_relat_1(A_8, k6_relat_1(A_28))=k7_relat_1(k6_relat_1(A_8), A_28) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_10])).
% 1.64/1.15  tff(c_95, plain, (![A_8, A_28]: (k8_relat_1(A_8, k6_relat_1(A_28))=k7_relat_1(k6_relat_1(A_8), A_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_82])).
% 1.64/1.15  tff(c_18, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.64/1.15  tff(c_112, plain, (![A_32, B_33]: (k8_relat_1(A_32, B_33)=B_33 | ~r1_tarski(k2_relat_1(B_33), A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.15  tff(c_115, plain, (![A_32, A_14]: (k8_relat_1(A_32, k6_relat_1(A_14))=k6_relat_1(A_14) | ~r1_tarski(A_14, A_32) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_112])).
% 1.64/1.15  tff(c_132, plain, (![A_36, A_37]: (k7_relat_1(k6_relat_1(A_36), A_37)=k6_relat_1(A_37) | ~r1_tarski(A_37, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_95, c_115])).
% 1.64/1.15  tff(c_14, plain, (![B_13, A_12]: (k7_relat_1(B_13, k3_xboole_0(k1_relat_1(B_13), A_12))=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.15  tff(c_139, plain, (![A_36, A_12]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_36)), A_12))=k7_relat_1(k6_relat_1(A_36), A_12) | ~v1_relat_1(k6_relat_1(A_36)) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_36)), A_12), A_36))), inference(superposition, [status(thm), theory('equality')], [c_132, c_14])).
% 1.64/1.15  tff(c_152, plain, (![A_36, A_12]: (k7_relat_1(k6_relat_1(A_36), A_12)=k6_relat_1(k3_xboole_0(A_36, A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16, c_8, c_16, c_139])).
% 1.64/1.15  tff(c_61, plain, (![B_26, A_27]: (k5_relat_1(B_26, k6_relat_1(A_27))=k8_relat_1(A_27, B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.15  tff(c_22, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.64/1.15  tff(c_67, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_22])).
% 1.64/1.15  tff(c_73, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_67])).
% 1.64/1.15  tff(c_101, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_73])).
% 1.64/1.15  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_101])).
% 1.64/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.15  
% 1.64/1.15  Inference rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Ref     : 0
% 1.64/1.15  #Sup     : 27
% 1.64/1.15  #Fact    : 0
% 1.64/1.15  #Define  : 0
% 1.64/1.15  #Split   : 0
% 1.64/1.15  #Chain   : 0
% 1.64/1.15  #Close   : 0
% 1.64/1.15  
% 1.64/1.15  Ordering : KBO
% 1.64/1.15  
% 1.64/1.15  Simplification rules
% 1.64/1.15  ----------------------
% 1.64/1.15  #Subsume      : 1
% 1.64/1.15  #Demod        : 22
% 1.64/1.15  #Tautology    : 19
% 1.64/1.15  #SimpNegUnit  : 0
% 1.64/1.15  #BackRed      : 4
% 1.64/1.15  
% 1.64/1.15  #Partial instantiations: 0
% 1.64/1.15  #Strategies tried      : 1
% 1.64/1.15  
% 1.64/1.15  Timing (in seconds)
% 1.64/1.15  ----------------------
% 1.64/1.15  Preprocessing        : 0.27
% 1.64/1.15  Parsing              : 0.14
% 1.64/1.15  CNF conversion       : 0.01
% 1.64/1.15  Main loop            : 0.12
% 1.64/1.15  Inferencing          : 0.05
% 1.64/1.16  Reduction            : 0.04
% 1.64/1.16  Demodulation         : 0.03
% 1.64/1.16  BG Simplification    : 0.01
% 1.64/1.16  Subsumption          : 0.01
% 1.64/1.16  Abstraction          : 0.01
% 1.64/1.16  MUC search           : 0.00
% 1.64/1.16  Cooper               : 0.00
% 1.64/1.16  Total                : 0.41
% 1.64/1.16  Index Insertion      : 0.00
% 1.64/1.16  Index Deletion       : 0.00
% 1.64/1.16  Index Matching       : 0.00
% 1.64/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
