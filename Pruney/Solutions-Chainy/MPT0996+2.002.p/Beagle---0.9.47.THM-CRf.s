%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:51 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   49 (  63 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k7_relset_1(A,B,D,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25,plain,(
    ! [C_18,A_19,B_20] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_29,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_35,plain,(
    ! [C_26,B_27,A_28] :
      ( v5_relat_1(C_26,B_27)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_28,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_39,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k9_relat_1(B_7,A_6),k2_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    ! [B_29,A_30] :
      ( r1_tarski(k2_relat_1(B_29),A_30)
      | ~ v5_relat_1(B_29,A_30)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_44,A_45,B_46] :
      ( r1_tarski(A_44,A_45)
      | ~ r1_tarski(A_44,k2_relat_1(B_46))
      | ~ v5_relat_1(B_46,A_45)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_40,c_2])).

tff(c_82,plain,(
    ! [B_47,A_48,A_49] :
      ( r1_tarski(k9_relat_1(B_47,A_48),A_49)
      | ~ v5_relat_1(B_47,A_49)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_60,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k7_relset_1(A_39,B_40,C_41,D_42) = k9_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_63,plain,(
    ! [D_42] : k7_relset_1('#skF_1','#skF_2','#skF_4',D_42) = k9_relat_1('#skF_4',D_42) ),
    inference(resolution,[status(thm)],[c_20,c_60])).

tff(c_18,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_18])).

tff(c_88,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_64])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_39,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.14  
% 1.80/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.80/1.15  
% 1.80/1.15  %Foreground sorts:
% 1.80/1.15  
% 1.80/1.15  
% 1.80/1.15  %Background operators:
% 1.80/1.15  
% 1.80/1.15  
% 1.80/1.15  %Foreground operators:
% 1.80/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.80/1.15  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 1.80/1.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.80/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.80/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.80/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.80/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.15  
% 1.80/1.16  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k7_relset_1(A, B, D, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_2)).
% 1.80/1.16  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.80/1.16  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.80/1.16  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 1.80/1.16  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 1.80/1.16  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.80/1.16  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.80/1.16  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.80/1.16  tff(c_25, plain, (![C_18, A_19, B_20]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.80/1.16  tff(c_29, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_25])).
% 1.80/1.16  tff(c_35, plain, (![C_26, B_27, A_28]: (v5_relat_1(C_26, B_27) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_28, B_27))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.80/1.16  tff(c_39, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_35])).
% 1.80/1.16  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k9_relat_1(B_7, A_6), k2_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.80/1.16  tff(c_40, plain, (![B_29, A_30]: (r1_tarski(k2_relat_1(B_29), A_30) | ~v5_relat_1(B_29, A_30) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.80/1.16  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.16  tff(c_74, plain, (![A_44, A_45, B_46]: (r1_tarski(A_44, A_45) | ~r1_tarski(A_44, k2_relat_1(B_46)) | ~v5_relat_1(B_46, A_45) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_40, c_2])).
% 1.80/1.16  tff(c_82, plain, (![B_47, A_48, A_49]: (r1_tarski(k9_relat_1(B_47, A_48), A_49) | ~v5_relat_1(B_47, A_49) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_8, c_74])).
% 1.80/1.16  tff(c_60, plain, (![A_39, B_40, C_41, D_42]: (k7_relset_1(A_39, B_40, C_41, D_42)=k9_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.80/1.16  tff(c_63, plain, (![D_42]: (k7_relset_1('#skF_1', '#skF_2', '#skF_4', D_42)=k9_relat_1('#skF_4', D_42))), inference(resolution, [status(thm)], [c_20, c_60])).
% 1.80/1.16  tff(c_18, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.80/1.16  tff(c_64, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_18])).
% 1.80/1.16  tff(c_88, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_64])).
% 1.80/1.16  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29, c_39, c_88])).
% 1.80/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.16  
% 1.80/1.16  Inference rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Ref     : 0
% 1.80/1.16  #Sup     : 16
% 1.80/1.16  #Fact    : 0
% 1.80/1.16  #Define  : 0
% 1.80/1.16  #Split   : 0
% 1.80/1.16  #Chain   : 0
% 1.80/1.16  #Close   : 0
% 1.80/1.16  
% 1.80/1.16  Ordering : KBO
% 1.80/1.16  
% 1.80/1.16  Simplification rules
% 1.80/1.16  ----------------------
% 1.80/1.16  #Subsume      : 0
% 1.80/1.16  #Demod        : 3
% 1.80/1.16  #Tautology    : 3
% 1.80/1.16  #SimpNegUnit  : 0
% 1.80/1.16  #BackRed      : 1
% 1.80/1.16  
% 1.80/1.16  #Partial instantiations: 0
% 1.80/1.16  #Strategies tried      : 1
% 1.80/1.16  
% 1.80/1.16  Timing (in seconds)
% 1.80/1.16  ----------------------
% 1.91/1.16  Preprocessing        : 0.28
% 1.91/1.16  Parsing              : 0.15
% 1.91/1.16  CNF conversion       : 0.02
% 1.91/1.16  Main loop            : 0.12
% 1.91/1.16  Inferencing          : 0.05
% 1.91/1.16  Reduction            : 0.03
% 1.91/1.16  Demodulation         : 0.02
% 1.91/1.16  BG Simplification    : 0.01
% 1.91/1.16  Subsumption          : 0.02
% 1.91/1.16  Abstraction          : 0.01
% 1.91/1.16  MUC search           : 0.00
% 1.91/1.16  Cooper               : 0.00
% 1.91/1.16  Total                : 0.43
% 1.91/1.16  Index Insertion      : 0.00
% 1.91/1.16  Index Deletion       : 0.00
% 1.91/1.16  Index Matching       : 0.00
% 1.91/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
