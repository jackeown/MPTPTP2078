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
% DateTime   : Thu Dec  3 10:13:53 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 (  59 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_24])).

tff(c_47,plain,(
    ! [C_33,A_34,B_35] :
      ( v4_relat_1(C_33,A_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k10_relat_1(B_7,A_6),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(k1_relat_1(B_29),A_30)
      | ~ v4_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_39,A_40,B_41] :
      ( r1_tarski(A_39,A_40)
      | ~ r1_tarski(A_39,k1_relat_1(B_41))
      | ~ v4_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_80,plain,(
    ! [B_47,A_48,A_49] :
      ( r1_tarski(k10_relat_1(B_47,A_48),A_49)
      | ~ v4_relat_1(B_47,A_49)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_58])).

tff(c_66,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k8_relset_1(A_42,B_43,C_44,D_45) = k10_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_69,plain,(
    ! [D_45] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_45) = k10_relat_1('#skF_4',D_45) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_18,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_18])).

tff(c_83,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_70])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_51,c_83])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.14  
% 1.73/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.14  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.73/1.14  
% 1.73/1.14  %Foreground sorts:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Background operators:
% 1.73/1.14  
% 1.73/1.14  
% 1.73/1.14  %Foreground operators:
% 1.73/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.14  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.73/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.73/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.73/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.73/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.73/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.14  
% 1.73/1.15  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 1.73/1.15  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.73/1.15  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.73/1.15  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.73/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.73/1.15  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.73/1.15  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.73/1.15  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.73/1.15  tff(c_24, plain, (![C_20, A_21, B_22]: (v1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.73/1.15  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_24])).
% 1.73/1.15  tff(c_47, plain, (![C_33, A_34, B_35]: (v4_relat_1(C_33, A_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.73/1.15  tff(c_51, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_47])).
% 1.73/1.15  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k10_relat_1(B_7, A_6), k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.73/1.15  tff(c_38, plain, (![B_29, A_30]: (r1_tarski(k1_relat_1(B_29), A_30) | ~v4_relat_1(B_29, A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.73/1.15  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.73/1.15  tff(c_58, plain, (![A_39, A_40, B_41]: (r1_tarski(A_39, A_40) | ~r1_tarski(A_39, k1_relat_1(B_41)) | ~v4_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_38, c_2])).
% 1.73/1.15  tff(c_80, plain, (![B_47, A_48, A_49]: (r1_tarski(k10_relat_1(B_47, A_48), A_49) | ~v4_relat_1(B_47, A_49) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_8, c_58])).
% 1.73/1.15  tff(c_66, plain, (![A_42, B_43, C_44, D_45]: (k8_relset_1(A_42, B_43, C_44, D_45)=k10_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.73/1.15  tff(c_69, plain, (![D_45]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_45)=k10_relat_1('#skF_4', D_45))), inference(resolution, [status(thm)], [c_20, c_66])).
% 1.73/1.15  tff(c_18, plain, (~r1_tarski(k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.73/1.15  tff(c_70, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_18])).
% 1.73/1.15  tff(c_83, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_70])).
% 1.73/1.15  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_51, c_83])).
% 1.73/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.15  
% 1.73/1.15  Inference rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Ref     : 0
% 1.73/1.15  #Sup     : 16
% 1.73/1.15  #Fact    : 0
% 1.73/1.15  #Define  : 0
% 1.73/1.15  #Split   : 0
% 1.73/1.15  #Chain   : 0
% 1.73/1.15  #Close   : 0
% 1.73/1.15  
% 1.73/1.15  Ordering : KBO
% 1.73/1.15  
% 1.73/1.15  Simplification rules
% 1.73/1.15  ----------------------
% 1.73/1.15  #Subsume      : 0
% 1.73/1.15  #Demod        : 3
% 1.73/1.15  #Tautology    : 3
% 1.73/1.15  #SimpNegUnit  : 0
% 1.73/1.15  #BackRed      : 1
% 1.73/1.15  
% 1.73/1.15  #Partial instantiations: 0
% 1.73/1.15  #Strategies tried      : 1
% 1.73/1.15  
% 1.73/1.15  Timing (in seconds)
% 1.73/1.15  ----------------------
% 1.73/1.15  Preprocessing        : 0.29
% 1.73/1.15  Parsing              : 0.16
% 1.73/1.15  CNF conversion       : 0.02
% 1.73/1.15  Main loop            : 0.11
% 1.73/1.15  Inferencing          : 0.05
% 1.73/1.15  Reduction            : 0.03
% 1.73/1.15  Demodulation         : 0.02
% 1.73/1.15  BG Simplification    : 0.01
% 1.73/1.15  Subsumption          : 0.02
% 1.73/1.15  Abstraction          : 0.01
% 1.73/1.15  MUC search           : 0.00
% 1.73/1.15  Cooper               : 0.00
% 1.73/1.15  Total                : 0.42
% 1.73/1.15  Index Insertion      : 0.00
% 1.73/1.15  Index Deletion       : 0.00
% 1.73/1.15  Index Matching       : 0.00
% 1.73/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
