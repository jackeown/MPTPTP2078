%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:29 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  64 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k8_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( k8_relat_1(A_9,k7_relat_1(C_11,B_10)) = k7_relat_1(k8_relat_1(A_9,C_11),B_10)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [B_28,A_29] :
      ( k3_xboole_0(k2_relat_1(B_28),A_29) = k2_relat_1(k8_relat_1(A_29,B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_236,plain,(
    ! [A_40,B_41,A_42] :
      ( k2_relat_1(k8_relat_1(A_40,k7_relat_1(B_41,A_42))) = k3_xboole_0(k9_relat_1(B_41,A_42),A_40)
      | ~ v1_relat_1(k7_relat_1(B_41,A_42))
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_77])).

tff(c_322,plain,(
    ! [A_46,C_47,B_48] :
      ( k2_relat_1(k7_relat_1(k8_relat_1(A_46,C_47),B_48)) = k3_xboole_0(k9_relat_1(C_47,B_48),A_46)
      | ~ v1_relat_1(k7_relat_1(C_47,B_48))
      | ~ v1_relat_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_236])).

tff(c_600,plain,(
    ! [A_66,C_67,A_68] :
      ( k9_relat_1(k8_relat_1(A_66,C_67),A_68) = k3_xboole_0(k9_relat_1(C_67,A_68),A_66)
      | ~ v1_relat_1(k7_relat_1(C_67,A_68))
      | ~ v1_relat_1(C_67)
      | ~ v1_relat_1(C_67)
      | ~ v1_relat_1(k8_relat_1(A_66,C_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_322])).

tff(c_610,plain,(
    ! [A_69,A_70,B_71] :
      ( k9_relat_1(k8_relat_1(A_69,A_70),B_71) = k3_xboole_0(k9_relat_1(A_70,B_71),A_69)
      | ~ v1_relat_1(k8_relat_1(A_69,A_70))
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_16,c_600])).

tff(c_616,plain,(
    ! [A_72,B_73,B_74] :
      ( k9_relat_1(k8_relat_1(A_72,B_73),B_74) = k3_xboole_0(k9_relat_1(B_73,B_74),A_72)
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_610])).

tff(c_18,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_622,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3','#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_18])).

tff(c_632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_2,c_622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:26:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.42  
% 2.64/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.42  %$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.42  
% 2.64/1.42  %Foreground sorts:
% 2.64/1.42  
% 2.64/1.42  
% 2.64/1.42  %Background operators:
% 2.64/1.42  
% 2.64/1.42  
% 2.64/1.42  %Foreground operators:
% 2.64/1.42  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.64/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.64/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.64/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.64/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.64/1.42  
% 2.96/1.43  tff(f_60, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_funct_1)).
% 2.96/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.96/1.43  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.96/1.43  tff(f_53, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.96/1.43  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.96/1.43  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 2.96/1.43  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.96/1.43  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.43  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.43  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k8_relat_1(A_5, B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.96/1.43  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.96/1.43  tff(c_12, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.96/1.43  tff(c_10, plain, (![A_9, C_11, B_10]: (k8_relat_1(A_9, k7_relat_1(C_11, B_10))=k7_relat_1(k8_relat_1(A_9, C_11), B_10) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.96/1.43  tff(c_77, plain, (![B_28, A_29]: (k3_xboole_0(k2_relat_1(B_28), A_29)=k2_relat_1(k8_relat_1(A_29, B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.43  tff(c_236, plain, (![A_40, B_41, A_42]: (k2_relat_1(k8_relat_1(A_40, k7_relat_1(B_41, A_42)))=k3_xboole_0(k9_relat_1(B_41, A_42), A_40) | ~v1_relat_1(k7_relat_1(B_41, A_42)) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_12, c_77])).
% 2.96/1.43  tff(c_322, plain, (![A_46, C_47, B_48]: (k2_relat_1(k7_relat_1(k8_relat_1(A_46, C_47), B_48))=k3_xboole_0(k9_relat_1(C_47, B_48), A_46) | ~v1_relat_1(k7_relat_1(C_47, B_48)) | ~v1_relat_1(C_47) | ~v1_relat_1(C_47))), inference(superposition, [status(thm), theory('equality')], [c_10, c_236])).
% 2.96/1.43  tff(c_600, plain, (![A_66, C_67, A_68]: (k9_relat_1(k8_relat_1(A_66, C_67), A_68)=k3_xboole_0(k9_relat_1(C_67, A_68), A_66) | ~v1_relat_1(k7_relat_1(C_67, A_68)) | ~v1_relat_1(C_67) | ~v1_relat_1(C_67) | ~v1_relat_1(k8_relat_1(A_66, C_67)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_322])).
% 2.96/1.43  tff(c_610, plain, (![A_69, A_70, B_71]: (k9_relat_1(k8_relat_1(A_69, A_70), B_71)=k3_xboole_0(k9_relat_1(A_70, B_71), A_69) | ~v1_relat_1(k8_relat_1(A_69, A_70)) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_16, c_600])).
% 2.96/1.43  tff(c_616, plain, (![A_72, B_73, B_74]: (k9_relat_1(k8_relat_1(A_72, B_73), B_74)=k3_xboole_0(k9_relat_1(B_73, B_74), A_72) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73))), inference(resolution, [status(thm)], [c_6, c_610])).
% 2.96/1.43  tff(c_18, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.96/1.43  tff(c_622, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_616, c_18])).
% 2.96/1.43  tff(c_632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_2, c_622])).
% 2.96/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.43  
% 2.96/1.43  Inference rules
% 2.96/1.43  ----------------------
% 2.96/1.43  #Ref     : 0
% 2.96/1.43  #Sup     : 169
% 2.96/1.43  #Fact    : 0
% 2.96/1.43  #Define  : 0
% 2.96/1.43  #Split   : 0
% 2.96/1.43  #Chain   : 0
% 2.96/1.43  #Close   : 0
% 2.96/1.43  
% 2.96/1.43  Ordering : KBO
% 2.96/1.43  
% 2.96/1.43  Simplification rules
% 2.96/1.43  ----------------------
% 2.96/1.43  #Subsume      : 18
% 2.96/1.43  #Demod        : 3
% 2.96/1.43  #Tautology    : 41
% 2.96/1.43  #SimpNegUnit  : 0
% 2.96/1.43  #BackRed      : 0
% 2.96/1.43  
% 2.96/1.43  #Partial instantiations: 0
% 2.96/1.43  #Strategies tried      : 1
% 2.96/1.43  
% 2.96/1.43  Timing (in seconds)
% 2.96/1.43  ----------------------
% 2.96/1.44  Preprocessing        : 0.29
% 2.96/1.44  Parsing              : 0.16
% 2.96/1.44  CNF conversion       : 0.02
% 2.96/1.44  Main loop            : 0.34
% 2.96/1.44  Inferencing          : 0.15
% 2.96/1.44  Reduction            : 0.09
% 2.96/1.44  Demodulation         : 0.07
% 2.96/1.44  BG Simplification    : 0.03
% 2.96/1.44  Subsumption          : 0.06
% 2.96/1.44  Abstraction          : 0.02
% 2.96/1.44  MUC search           : 0.00
% 2.96/1.44  Cooper               : 0.00
% 2.96/1.44  Total                : 0.66
% 2.96/1.44  Index Insertion      : 0.00
% 2.96/1.44  Index Deletion       : 0.00
% 2.96/1.44  Index Matching       : 0.00
% 2.96/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
