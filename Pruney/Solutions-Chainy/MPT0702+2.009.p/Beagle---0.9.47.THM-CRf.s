%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:03 EST 2020

% Result     : Theorem 12.79s
% Output     : CNFRefutation 12.89s
% Verified   : 
% Statistics : Number of formulae       :   56 (  66 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 122 expanded)
%              Number of equality atoms :   30 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_47,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

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
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_125,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_133,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_125,c_22])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_15,B_16] : k6_subset_1(A_15,B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [C_21,A_19,B_20] :
      ( k6_subset_1(k9_relat_1(C_21,A_19),k9_relat_1(C_21,B_20)) = k9_relat_1(C_21,k6_subset_1(A_19,B_20))
      | ~ v2_funct_1(C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_839,plain,(
    ! [C_67,A_68,B_69] :
      ( k4_xboole_0(k9_relat_1(C_67,A_68),k9_relat_1(C_67,B_69)) = k9_relat_1(C_67,k4_xboole_0(A_68,B_69))
      | ~ v2_funct_1(C_67)
      | ~ v1_funct_1(C_67)
      | ~ v1_relat_1(C_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_20])).

tff(c_28,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_134,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_155,plain,(
    k4_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_134])).

tff(c_852,plain,
    ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_155])).

tff(c_866,plain,(
    k9_relat_1('#skF_3',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_852])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_93,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_109,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_217,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_242,plain,(
    ! [A_43,B_44,B_45] : r1_tarski(A_43,k2_xboole_0(k2_xboole_0(A_43,B_44),B_45)) ),
    inference(resolution,[status(thm)],[c_14,c_217])).

tff(c_255,plain,(
    ! [B_45] : r1_tarski('#skF_1',k2_xboole_0(k1_relat_1('#skF_3'),B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_242])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k4_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_637,plain,(
    ! [B_63,A_64] :
      ( k9_relat_1(B_63,A_64) != k1_xboole_0
      | ~ r1_tarski(A_64,k1_relat_1(B_63))
      | k1_xboole_0 = A_64
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4016,plain,(
    ! [B_141,A_142,B_143] :
      ( k9_relat_1(B_141,k4_xboole_0(A_142,B_143)) != k1_xboole_0
      | k4_xboole_0(A_142,B_143) = k1_xboole_0
      | ~ v1_relat_1(B_141)
      | ~ r1_tarski(A_142,k2_xboole_0(B_143,k1_relat_1(B_141))) ) ),
    inference(resolution,[status(thm)],[c_12,c_637])).

tff(c_23003,plain,(
    ! [B_340,A_341,A_342] :
      ( k9_relat_1(B_340,k4_xboole_0(A_341,A_342)) != k1_xboole_0
      | k4_xboole_0(A_341,A_342) = k1_xboole_0
      | ~ v1_relat_1(B_340)
      | ~ r1_tarski(A_341,k2_xboole_0(k1_relat_1(B_340),A_342)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4016])).

tff(c_23179,plain,(
    ! [B_45] :
      ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1',B_45)) != k1_xboole_0
      | k4_xboole_0('#skF_1',B_45) = k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_255,c_23003])).

tff(c_45655,plain,(
    ! [B_515] :
      ( k9_relat_1('#skF_3',k4_xboole_0('#skF_1',B_515)) != k1_xboole_0
      | k4_xboole_0('#skF_1',B_515) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_23179])).

tff(c_45700,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_45655])).

tff(c_45743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_45700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.79/5.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.79/5.96  
% 12.79/5.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.79/5.97  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.79/5.97  
% 12.79/5.97  %Foreground sorts:
% 12.79/5.97  
% 12.79/5.97  
% 12.79/5.97  %Background operators:
% 12.79/5.97  
% 12.79/5.97  
% 12.79/5.97  %Foreground operators:
% 12.79/5.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.79/5.97  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.79/5.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.79/5.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.79/5.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.79/5.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.79/5.97  tff('#skF_2', type, '#skF_2': $i).
% 12.79/5.97  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.79/5.97  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.79/5.97  tff('#skF_3', type, '#skF_3': $i).
% 12.79/5.97  tff('#skF_1', type, '#skF_1': $i).
% 12.79/5.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.79/5.97  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.79/5.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.79/5.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.79/5.97  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.79/5.97  
% 12.89/5.98  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.89/5.98  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 12.89/5.98  tff(f_47, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.89/5.98  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 12.89/5.98  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.89/5.98  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 12.89/5.98  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 12.89/5.98  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.89/5.98  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 12.89/5.98  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 12.89/5.98  tff(c_125, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.89/5.98  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.89/5.98  tff(c_133, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_125, c_22])).
% 12.89/5.98  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.89/5.98  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.89/5.98  tff(c_24, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.89/5.98  tff(c_16, plain, (![A_15, B_16]: (k6_subset_1(A_15, B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.89/5.98  tff(c_20, plain, (![C_21, A_19, B_20]: (k6_subset_1(k9_relat_1(C_21, A_19), k9_relat_1(C_21, B_20))=k9_relat_1(C_21, k6_subset_1(A_19, B_20)) | ~v2_funct_1(C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.89/5.98  tff(c_839, plain, (![C_67, A_68, B_69]: (k4_xboole_0(k9_relat_1(C_67, A_68), k9_relat_1(C_67, B_69))=k9_relat_1(C_67, k4_xboole_0(A_68, B_69)) | ~v2_funct_1(C_67) | ~v1_funct_1(C_67) | ~v1_relat_1(C_67))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_20])).
% 12.89/5.98  tff(c_28, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.89/5.98  tff(c_134, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.89/5.98  tff(c_155, plain, (k4_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_134])).
% 12.89/5.98  tff(c_852, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_839, c_155])).
% 12.89/5.98  tff(c_866, plain, (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_852])).
% 12.89/5.98  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 12.89/5.98  tff(c_93, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.89/5.98  tff(c_109, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_93])).
% 12.89/5.98  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.89/5.98  tff(c_217, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.89/5.98  tff(c_242, plain, (![A_43, B_44, B_45]: (r1_tarski(A_43, k2_xboole_0(k2_xboole_0(A_43, B_44), B_45)))), inference(resolution, [status(thm)], [c_14, c_217])).
% 12.89/5.98  tff(c_255, plain, (![B_45]: (r1_tarski('#skF_1', k2_xboole_0(k1_relat_1('#skF_3'), B_45)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_242])).
% 12.89/5.98  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.89/5.98  tff(c_12, plain, (![A_10, B_11, C_12]: (r1_tarski(k4_xboole_0(A_10, B_11), C_12) | ~r1_tarski(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.89/5.98  tff(c_637, plain, (![B_63, A_64]: (k9_relat_1(B_63, A_64)!=k1_xboole_0 | ~r1_tarski(A_64, k1_relat_1(B_63)) | k1_xboole_0=A_64 | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.89/5.98  tff(c_4016, plain, (![B_141, A_142, B_143]: (k9_relat_1(B_141, k4_xboole_0(A_142, B_143))!=k1_xboole_0 | k4_xboole_0(A_142, B_143)=k1_xboole_0 | ~v1_relat_1(B_141) | ~r1_tarski(A_142, k2_xboole_0(B_143, k1_relat_1(B_141))))), inference(resolution, [status(thm)], [c_12, c_637])).
% 12.89/5.98  tff(c_23003, plain, (![B_340, A_341, A_342]: (k9_relat_1(B_340, k4_xboole_0(A_341, A_342))!=k1_xboole_0 | k4_xboole_0(A_341, A_342)=k1_xboole_0 | ~v1_relat_1(B_340) | ~r1_tarski(A_341, k2_xboole_0(k1_relat_1(B_340), A_342)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4016])).
% 12.89/5.98  tff(c_23179, plain, (![B_45]: (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', B_45))!=k1_xboole_0 | k4_xboole_0('#skF_1', B_45)=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_255, c_23003])).
% 12.89/5.98  tff(c_45655, plain, (![B_515]: (k9_relat_1('#skF_3', k4_xboole_0('#skF_1', B_515))!=k1_xboole_0 | k4_xboole_0('#skF_1', B_515)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_23179])).
% 12.89/5.98  tff(c_45700, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_866, c_45655])).
% 12.89/5.98  tff(c_45743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_45700])).
% 12.89/5.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.89/5.98  
% 12.89/5.98  Inference rules
% 12.89/5.98  ----------------------
% 12.89/5.98  #Ref     : 0
% 12.89/5.98  #Sup     : 10707
% 12.89/5.98  #Fact    : 0
% 12.89/5.98  #Define  : 0
% 12.89/5.98  #Split   : 1
% 12.89/5.98  #Chain   : 0
% 12.89/5.98  #Close   : 0
% 12.89/5.98  
% 12.89/5.98  Ordering : KBO
% 12.89/5.98  
% 12.89/5.98  Simplification rules
% 12.89/5.98  ----------------------
% 12.89/5.98  #Subsume      : 339
% 12.89/5.98  #Demod        : 11040
% 12.89/5.98  #Tautology    : 8061
% 12.89/5.98  #SimpNegUnit  : 2
% 12.89/5.98  #BackRed      : 0
% 12.89/5.98  
% 12.89/5.98  #Partial instantiations: 0
% 12.89/5.98  #Strategies tried      : 1
% 12.89/5.98  
% 12.89/5.98  Timing (in seconds)
% 12.89/5.98  ----------------------
% 12.89/5.98  Preprocessing        : 0.29
% 12.89/5.98  Parsing              : 0.15
% 12.89/5.98  CNF conversion       : 0.02
% 12.89/5.98  Main loop            : 4.89
% 12.89/5.98  Inferencing          : 0.82
% 12.89/5.98  Reduction            : 2.77
% 12.89/5.98  Demodulation         : 2.48
% 12.89/5.98  BG Simplification    : 0.09
% 12.89/5.98  Subsumption          : 0.97
% 12.89/5.98  Abstraction          : 0.14
% 12.89/5.98  MUC search           : 0.00
% 12.89/5.98  Cooper               : 0.00
% 12.89/5.98  Total                : 5.21
% 12.89/5.98  Index Insertion      : 0.00
% 12.89/5.98  Index Deletion       : 0.00
% 12.89/5.98  Index Matching       : 0.00
% 12.89/5.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
