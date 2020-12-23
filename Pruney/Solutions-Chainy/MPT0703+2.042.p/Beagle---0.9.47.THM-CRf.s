%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:14 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  93 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_229,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_241,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_229,c_18])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [C_16,A_14,B_15] :
      ( k6_subset_1(k10_relat_1(C_16,A_14),k10_relat_1(C_16,B_15)) = k10_relat_1(C_16,k6_subset_1(A_14,B_15))
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_539,plain,(
    ! [C_52,A_53,B_54] :
      ( k4_xboole_0(k10_relat_1(C_52,A_53),k10_relat_1(C_52,B_54)) = k10_relat_1(C_52,k4_xboole_0(A_53,B_54))
      | ~ v1_funct_1(C_52)
      | ~ v1_relat_1(C_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_16])).

tff(c_22,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_4])).

tff(c_554,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_61])).

tff(c_576,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_554])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_10,c_126])).

tff(c_242,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,C_36)
      | ~ r1_tarski(k2_xboole_0(A_35,B_37),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_450,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(k4_xboole_0(A_47,B_48),C_49)
      | ~ r1_tarski(A_47,C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_242])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k10_relat_1(B_13,A_12) != k1_xboole_0
      | ~ r1_tarski(A_12,k2_relat_1(B_13))
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14846,plain,(
    ! [B_332,A_333,B_334] :
      ( k10_relat_1(B_332,k4_xboole_0(A_333,B_334)) != k1_xboole_0
      | k4_xboole_0(A_333,B_334) = k1_xboole_0
      | ~ v1_relat_1(B_332)
      | ~ r1_tarski(A_333,k2_relat_1(B_332)) ) ),
    inference(resolution,[status(thm)],[c_450,c_14])).

tff(c_14902,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_14846])).

tff(c_14936,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26,c_14902])).

tff(c_14938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_14936])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.92/2.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.92/2.95  
% 7.92/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.92/2.96  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.92/2.96  
% 7.92/2.96  %Foreground sorts:
% 7.92/2.96  
% 7.92/2.96  
% 7.92/2.96  %Background operators:
% 7.92/2.96  
% 7.92/2.96  
% 7.92/2.96  %Foreground operators:
% 7.92/2.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.92/2.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.92/2.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.92/2.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.92/2.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.92/2.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.92/2.96  tff('#skF_2', type, '#skF_2': $i).
% 7.92/2.96  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.92/2.96  tff('#skF_3', type, '#skF_3': $i).
% 7.92/2.96  tff('#skF_1', type, '#skF_1': $i).
% 7.92/2.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.92/2.96  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.92/2.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.92/2.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.92/2.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.92/2.96  
% 7.92/2.97  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.92/2.97  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 7.92/2.97  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.92/2.97  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 7.92/2.97  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.92/2.97  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.92/2.97  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.92/2.97  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 7.92/2.97  tff(c_229, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.92/2.97  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.92/2.97  tff(c_241, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_229, c_18])).
% 7.92/2.97  tff(c_20, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.92/2.97  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.92/2.97  tff(c_24, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.92/2.97  tff(c_12, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.92/2.97  tff(c_16, plain, (![C_16, A_14, B_15]: (k6_subset_1(k10_relat_1(C_16, A_14), k10_relat_1(C_16, B_15))=k10_relat_1(C_16, k6_subset_1(A_14, B_15)) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.92/2.97  tff(c_539, plain, (![C_52, A_53, B_54]: (k4_xboole_0(k10_relat_1(C_52, A_53), k10_relat_1(C_52, B_54))=k10_relat_1(C_52, k4_xboole_0(A_53, B_54)) | ~v1_funct_1(C_52) | ~v1_relat_1(C_52))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_16])).
% 7.92/2.97  tff(c_22, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.92/2.97  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.92/2.97  tff(c_61, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_4])).
% 7.92/2.97  tff(c_554, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_539, c_61])).
% 7.92/2.97  tff(c_576, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_554])).
% 7.92/2.97  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.92/2.97  tff(c_126, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.92/2.97  tff(c_149, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_10, c_126])).
% 7.92/2.97  tff(c_242, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, C_36) | ~r1_tarski(k2_xboole_0(A_35, B_37), C_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.92/2.97  tff(c_450, plain, (![A_47, B_48, C_49]: (r1_tarski(k4_xboole_0(A_47, B_48), C_49) | ~r1_tarski(A_47, C_49))), inference(superposition, [status(thm), theory('equality')], [c_149, c_242])).
% 7.92/2.97  tff(c_14, plain, (![B_13, A_12]: (k10_relat_1(B_13, A_12)!=k1_xboole_0 | ~r1_tarski(A_12, k2_relat_1(B_13)) | k1_xboole_0=A_12 | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.92/2.97  tff(c_14846, plain, (![B_332, A_333, B_334]: (k10_relat_1(B_332, k4_xboole_0(A_333, B_334))!=k1_xboole_0 | k4_xboole_0(A_333, B_334)=k1_xboole_0 | ~v1_relat_1(B_332) | ~r1_tarski(A_333, k2_relat_1(B_332)))), inference(resolution, [status(thm)], [c_450, c_14])).
% 7.92/2.97  tff(c_14902, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_576, c_14846])).
% 7.92/2.97  tff(c_14936, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26, c_14902])).
% 7.92/2.97  tff(c_14938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_14936])).
% 7.92/2.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.92/2.97  
% 7.92/2.97  Inference rules
% 7.92/2.97  ----------------------
% 7.92/2.97  #Ref     : 0
% 7.92/2.97  #Sup     : 3679
% 7.92/2.97  #Fact    : 0
% 7.92/2.97  #Define  : 0
% 7.92/2.97  #Split   : 2
% 7.92/2.97  #Chain   : 0
% 7.92/2.97  #Close   : 0
% 7.92/2.97  
% 7.92/2.97  Ordering : KBO
% 7.92/2.97  
% 7.92/2.97  Simplification rules
% 7.92/2.97  ----------------------
% 7.92/2.97  #Subsume      : 361
% 7.92/2.97  #Demod        : 4105
% 7.92/2.97  #Tautology    : 2606
% 7.92/2.97  #SimpNegUnit  : 3
% 7.92/2.97  #BackRed      : 6
% 7.92/2.97  
% 7.92/2.97  #Partial instantiations: 0
% 7.92/2.97  #Strategies tried      : 1
% 7.92/2.97  
% 7.92/2.97  Timing (in seconds)
% 7.92/2.97  ----------------------
% 7.92/2.97  Preprocessing        : 0.39
% 7.92/2.97  Parsing              : 0.20
% 7.92/2.97  CNF conversion       : 0.03
% 7.92/2.97  Main loop            : 1.76
% 7.92/2.97  Inferencing          : 0.53
% 7.92/2.97  Reduction            : 0.67
% 7.92/2.97  Demodulation         : 0.52
% 7.92/2.97  BG Simplification    : 0.06
% 7.92/2.97  Subsumption          : 0.39
% 7.92/2.97  Abstraction          : 0.08
% 7.92/2.97  MUC search           : 0.00
% 7.92/2.97  Cooper               : 0.00
% 7.92/2.97  Total                : 2.18
% 7.92/2.97  Index Insertion      : 0.00
% 7.92/2.97  Index Deletion       : 0.00
% 7.92/2.97  Index Matching       : 0.00
% 7.92/2.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
