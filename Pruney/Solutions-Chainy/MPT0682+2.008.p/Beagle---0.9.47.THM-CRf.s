%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:29 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  67 expanded)
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

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k8_relat_1(A_14,B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( k8_relat_1(A_7,k7_relat_1(C_9,B_8)) = k7_relat_1(k8_relat_1(A_7,C_9),B_8)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [B_30,A_31] :
      ( k3_xboole_0(k2_relat_1(B_30),A_31) = k2_relat_1(k8_relat_1(A_31,B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_246,plain,(
    ! [A_45,B_46,A_47] :
      ( k2_relat_1(k8_relat_1(A_45,k7_relat_1(B_46,A_47))) = k3_xboole_0(k9_relat_1(B_46,A_47),A_45)
      | ~ v1_relat_1(k7_relat_1(B_46,A_47))
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_332,plain,(
    ! [A_51,C_52,B_53] :
      ( k2_relat_1(k7_relat_1(k8_relat_1(A_51,C_52),B_53)) = k3_xboole_0(k9_relat_1(C_52,B_53),A_51)
      | ~ v1_relat_1(k7_relat_1(C_52,B_53))
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_246])).

tff(c_559,plain,(
    ! [A_67,C_68,A_69] :
      ( k9_relat_1(k8_relat_1(A_67,C_68),A_69) = k3_xboole_0(k9_relat_1(C_68,A_69),A_67)
      | ~ v1_relat_1(k7_relat_1(C_68,A_69))
      | ~ v1_relat_1(C_68)
      | ~ v1_relat_1(C_68)
      | ~ v1_relat_1(k8_relat_1(A_67,C_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_332])).

tff(c_569,plain,(
    ! [A_70,A_71,B_72] :
      ( k9_relat_1(k8_relat_1(A_70,A_71),B_72) = k3_xboole_0(k9_relat_1(A_71,B_72),A_70)
      | ~ v1_relat_1(k8_relat_1(A_70,A_71))
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_14,c_559])).

tff(c_575,plain,(
    ! [A_73,B_74,B_75] :
      ( k9_relat_1(k8_relat_1(A_73,B_74),B_75) = k3_xboole_0(k9_relat_1(B_74,B_75),A_73)
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_18,c_569])).

tff(c_20,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_581,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3','#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_20])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_2,c_581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.37  %$ v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.37  
% 2.45/1.37  %Foreground sorts:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Background operators:
% 2.45/1.37  
% 2.45/1.37  
% 2.45/1.37  %Foreground operators:
% 2.45/1.37  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.45/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.45/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.45/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.45/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.45/1.37  
% 2.75/1.38  tff(f_64, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_funct_1)).
% 2.75/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.75/1.38  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_funct_1)).
% 2.75/1.38  tff(f_49, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.75/1.38  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.75/1.38  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 2.75/1.38  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.75/1.38  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.38  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.38  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k8_relat_1(A_14, B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.75/1.38  tff(c_14, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.38  tff(c_10, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.38  tff(c_8, plain, (![A_7, C_9, B_8]: (k8_relat_1(A_7, k7_relat_1(C_9, B_8))=k7_relat_1(k8_relat_1(A_7, C_9), B_8) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.75/1.38  tff(c_80, plain, (![B_30, A_31]: (k3_xboole_0(k2_relat_1(B_30), A_31)=k2_relat_1(k8_relat_1(A_31, B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.38  tff(c_246, plain, (![A_45, B_46, A_47]: (k2_relat_1(k8_relat_1(A_45, k7_relat_1(B_46, A_47)))=k3_xboole_0(k9_relat_1(B_46, A_47), A_45) | ~v1_relat_1(k7_relat_1(B_46, A_47)) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_80])).
% 2.75/1.38  tff(c_332, plain, (![A_51, C_52, B_53]: (k2_relat_1(k7_relat_1(k8_relat_1(A_51, C_52), B_53))=k3_xboole_0(k9_relat_1(C_52, B_53), A_51) | ~v1_relat_1(k7_relat_1(C_52, B_53)) | ~v1_relat_1(C_52) | ~v1_relat_1(C_52))), inference(superposition, [status(thm), theory('equality')], [c_8, c_246])).
% 2.75/1.38  tff(c_559, plain, (![A_67, C_68, A_69]: (k9_relat_1(k8_relat_1(A_67, C_68), A_69)=k3_xboole_0(k9_relat_1(C_68, A_69), A_67) | ~v1_relat_1(k7_relat_1(C_68, A_69)) | ~v1_relat_1(C_68) | ~v1_relat_1(C_68) | ~v1_relat_1(k8_relat_1(A_67, C_68)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_332])).
% 2.75/1.38  tff(c_569, plain, (![A_70, A_71, B_72]: (k9_relat_1(k8_relat_1(A_70, A_71), B_72)=k3_xboole_0(k9_relat_1(A_71, B_72), A_70) | ~v1_relat_1(k8_relat_1(A_70, A_71)) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_14, c_559])).
% 2.75/1.38  tff(c_575, plain, (![A_73, B_74, B_75]: (k9_relat_1(k8_relat_1(A_73, B_74), B_75)=k3_xboole_0(k9_relat_1(B_74, B_75), A_73) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_18, c_569])).
% 2.75/1.38  tff(c_20, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.75/1.38  tff(c_581, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_575, c_20])).
% 2.75/1.38  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_2, c_581])).
% 2.75/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  Inference rules
% 2.75/1.38  ----------------------
% 2.75/1.38  #Ref     : 0
% 2.75/1.38  #Sup     : 157
% 2.75/1.38  #Fact    : 0
% 2.75/1.38  #Define  : 0
% 2.75/1.38  #Split   : 0
% 2.75/1.38  #Chain   : 0
% 2.75/1.38  #Close   : 0
% 2.75/1.38  
% 2.75/1.38  Ordering : KBO
% 2.75/1.38  
% 2.75/1.38  Simplification rules
% 2.75/1.38  ----------------------
% 2.75/1.38  #Subsume      : 19
% 2.75/1.38  #Demod        : 3
% 2.75/1.38  #Tautology    : 39
% 2.75/1.38  #SimpNegUnit  : 0
% 2.75/1.38  #BackRed      : 0
% 2.75/1.38  
% 2.75/1.38  #Partial instantiations: 0
% 2.75/1.38  #Strategies tried      : 1
% 2.75/1.38  
% 2.75/1.38  Timing (in seconds)
% 2.75/1.38  ----------------------
% 2.75/1.38  Preprocessing        : 0.29
% 2.75/1.38  Parsing              : 0.16
% 2.75/1.38  CNF conversion       : 0.02
% 2.75/1.38  Main loop            : 0.33
% 2.75/1.38  Inferencing          : 0.14
% 2.75/1.38  Reduction            : 0.09
% 2.75/1.38  Demodulation         : 0.07
% 2.75/1.38  BG Simplification    : 0.03
% 2.75/1.39  Subsumption          : 0.06
% 2.75/1.39  Abstraction          : 0.02
% 2.75/1.39  MUC search           : 0.00
% 2.75/1.39  Cooper               : 0.00
% 2.75/1.39  Total                : 0.65
% 2.75/1.39  Index Insertion      : 0.00
% 2.75/1.39  Index Deletion       : 0.00
% 2.75/1.39  Index Matching       : 0.00
% 2.75/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
