%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:09 EST 2020

% Result     : Theorem 12.38s
% Output     : CNFRefutation 12.38s
% Verified   : 
% Statistics : Number of formulae       :   54 (  63 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 105 expanded)
%              Number of equality atoms :   30 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k2_relat_1(B))
          & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(c_148,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_160,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_148,c_22])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    ! [A_15,B_16] : k6_subset_1(A_15,B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [C_21,A_19,B_20] :
      ( k6_subset_1(k10_relat_1(C_21,A_19),k10_relat_1(C_21,B_20)) = k10_relat_1(C_21,k6_subset_1(A_19,B_20))
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_879,plain,(
    ! [C_67,A_68,B_69] :
      ( k4_xboole_0(k10_relat_1(C_67,A_68),k10_relat_1(C_67,B_69)) = k10_relat_1(C_67,k4_xboole_0(A_68,B_69))
      | ~ v1_funct_1(C_67)
      | ~ v1_relat_1(C_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_20])).

tff(c_26,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_123,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    k4_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_123])).

tff(c_892,plain,
    ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_140])).

tff(c_906,plain,(
    k10_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_892])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_91,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_91])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_235,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_263,plain,(
    ! [A_43,B_44,B_45] : r1_tarski(A_43,k2_xboole_0(k2_xboole_0(A_43,B_44),B_45)) ),
    inference(resolution,[status(thm)],[c_14,c_235])).

tff(c_279,plain,(
    ! [B_45] : r1_tarski('#skF_1',k2_xboole_0(k2_relat_1('#skF_3'),B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_263])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_676,plain,(
    ! [B_63,A_64] :
      ( k10_relat_1(B_63,A_64) != k1_xboole_0
      | ~ r1_tarski(A_64,k2_relat_1(B_63))
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3973,plain,(
    ! [B_137,A_138,B_139] :
      ( k10_relat_1(B_137,k4_xboole_0(A_138,B_139)) != k1_xboole_0
      | k4_xboole_0(A_138,B_139) = k1_xboole_0
      | ~ v1_relat_1(B_137)
      | ~ r1_tarski(A_138,k2_xboole_0(B_139,k2_relat_1(B_137))) ) ),
    inference(resolution,[status(thm)],[c_12,c_676])).

tff(c_25401,plain,(
    ! [B_345,A_346,A_347] :
      ( k10_relat_1(B_345,k4_xboole_0(A_346,A_347)) != k1_xboole_0
      | k4_xboole_0(A_346,A_347) = k1_xboole_0
      | ~ v1_relat_1(B_345)
      | ~ r1_tarski(A_346,k2_xboole_0(k2_relat_1(B_345),A_347)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3973])).

tff(c_25585,plain,(
    ! [B_45] :
      ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1',B_45)) != k1_xboole_0
      | k4_xboole_0('#skF_1',B_45) = k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_279,c_25401])).

tff(c_40107,plain,(
    ! [B_457] :
      ( k10_relat_1('#skF_3',k4_xboole_0('#skF_1',B_457)) != k1_xboole_0
      | k4_xboole_0('#skF_1',B_457) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_25585])).

tff(c_40148,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_40107])).

tff(c_40189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_40148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.38/5.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.38/5.34  
% 12.38/5.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.38/5.34  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.38/5.34  
% 12.38/5.34  %Foreground sorts:
% 12.38/5.34  
% 12.38/5.34  
% 12.38/5.34  %Background operators:
% 12.38/5.34  
% 12.38/5.34  
% 12.38/5.34  %Foreground operators:
% 12.38/5.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.38/5.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.38/5.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.38/5.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.38/5.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.38/5.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.38/5.34  tff('#skF_2', type, '#skF_2': $i).
% 12.38/5.34  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.38/5.34  tff('#skF_3', type, '#skF_3': $i).
% 12.38/5.34  tff('#skF_1', type, '#skF_1': $i).
% 12.38/5.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.38/5.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.38/5.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.38/5.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.38/5.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.38/5.34  
% 12.38/5.35  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.38/5.35  tff(f_74, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 12.38/5.35  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.38/5.35  tff(f_63, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_funct_1)).
% 12.38/5.35  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.38/5.35  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.38/5.35  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 12.38/5.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.38/5.35  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 12.38/5.35  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 12.38/5.35  tff(c_148, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.38/5.35  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.38/5.35  tff(c_160, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_148, c_22])).
% 12.38/5.35  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.38/5.35  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.38/5.35  tff(c_16, plain, (![A_15, B_16]: (k6_subset_1(A_15, B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.38/5.35  tff(c_20, plain, (![C_21, A_19, B_20]: (k6_subset_1(k10_relat_1(C_21, A_19), k10_relat_1(C_21, B_20))=k10_relat_1(C_21, k6_subset_1(A_19, B_20)) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.38/5.35  tff(c_879, plain, (![C_67, A_68, B_69]: (k4_xboole_0(k10_relat_1(C_67, A_68), k10_relat_1(C_67, B_69))=k10_relat_1(C_67, k4_xboole_0(A_68, B_69)) | ~v1_funct_1(C_67) | ~v1_relat_1(C_67))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_20])).
% 12.38/5.35  tff(c_26, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.38/5.35  tff(c_123, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.38/5.35  tff(c_140, plain, (k4_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_123])).
% 12.38/5.35  tff(c_892, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_879, c_140])).
% 12.38/5.35  tff(c_906, plain, (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_892])).
% 12.38/5.35  tff(c_24, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.38/5.35  tff(c_91, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.38/5.35  tff(c_107, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_91])).
% 12.38/5.35  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.38/5.35  tff(c_235, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.38/5.35  tff(c_263, plain, (![A_43, B_44, B_45]: (r1_tarski(A_43, k2_xboole_0(k2_xboole_0(A_43, B_44), B_45)))), inference(resolution, [status(thm)], [c_14, c_235])).
% 12.38/5.35  tff(c_279, plain, (![B_45]: (r1_tarski('#skF_1', k2_xboole_0(k2_relat_1('#skF_3'), B_45)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_263])).
% 12.38/5.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.38/5.35  tff(c_12, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.38/5.35  tff(c_676, plain, (![B_63, A_64]: (k10_relat_1(B_63, A_64)!=k1_xboole_0 | ~r1_tarski(A_64, k2_relat_1(B_63)) | k1_xboole_0=A_64 | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.38/5.35  tff(c_3973, plain, (![B_137, A_138, B_139]: (k10_relat_1(B_137, k4_xboole_0(A_138, B_139))!=k1_xboole_0 | k4_xboole_0(A_138, B_139)=k1_xboole_0 | ~v1_relat_1(B_137) | ~r1_tarski(A_138, k2_xboole_0(B_139, k2_relat_1(B_137))))), inference(resolution, [status(thm)], [c_12, c_676])).
% 12.38/5.35  tff(c_25401, plain, (![B_345, A_346, A_347]: (k10_relat_1(B_345, k4_xboole_0(A_346, A_347))!=k1_xboole_0 | k4_xboole_0(A_346, A_347)=k1_xboole_0 | ~v1_relat_1(B_345) | ~r1_tarski(A_346, k2_xboole_0(k2_relat_1(B_345), A_347)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3973])).
% 12.38/5.35  tff(c_25585, plain, (![B_45]: (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', B_45))!=k1_xboole_0 | k4_xboole_0('#skF_1', B_45)=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_279, c_25401])).
% 12.38/5.35  tff(c_40107, plain, (![B_457]: (k10_relat_1('#skF_3', k4_xboole_0('#skF_1', B_457))!=k1_xboole_0 | k4_xboole_0('#skF_1', B_457)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_25585])).
% 12.38/5.35  tff(c_40148, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_906, c_40107])).
% 12.38/5.35  tff(c_40189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_40148])).
% 12.38/5.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.38/5.35  
% 12.38/5.35  Inference rules
% 12.38/5.35  ----------------------
% 12.38/5.35  #Ref     : 0
% 12.38/5.35  #Sup     : 9397
% 12.38/5.35  #Fact    : 0
% 12.38/5.35  #Define  : 0
% 12.38/5.35  #Split   : 1
% 12.38/5.35  #Chain   : 0
% 12.38/5.35  #Close   : 0
% 12.38/5.35  
% 12.38/5.35  Ordering : KBO
% 12.38/5.35  
% 12.38/5.35  Simplification rules
% 12.38/5.35  ----------------------
% 12.38/5.35  #Subsume      : 348
% 12.38/5.35  #Demod        : 9673
% 12.38/5.35  #Tautology    : 7012
% 12.38/5.35  #SimpNegUnit  : 2
% 12.38/5.35  #BackRed      : 0
% 12.38/5.35  
% 12.38/5.35  #Partial instantiations: 0
% 12.38/5.35  #Strategies tried      : 1
% 12.38/5.35  
% 12.38/5.35  Timing (in seconds)
% 12.38/5.35  ----------------------
% 12.38/5.35  Preprocessing        : 0.29
% 12.38/5.35  Parsing              : 0.16
% 12.38/5.35  CNF conversion       : 0.02
% 12.38/5.35  Main loop            : 4.31
% 12.38/5.35  Inferencing          : 0.72
% 12.38/5.35  Reduction            : 2.48
% 12.38/5.35  Demodulation         : 2.23
% 12.38/5.35  BG Simplification    : 0.08
% 12.38/5.35  Subsumption          : 0.83
% 12.38/5.35  Abstraction          : 0.13
% 12.38/5.35  MUC search           : 0.00
% 12.38/5.35  Cooper               : 0.00
% 12.38/5.35  Total                : 4.62
% 12.38/5.35  Index Insertion      : 0.00
% 12.38/5.35  Index Deletion       : 0.00
% 12.38/5.35  Index Matching       : 0.00
% 12.38/5.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
