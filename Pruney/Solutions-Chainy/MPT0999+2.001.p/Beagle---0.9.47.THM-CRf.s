%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:53 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   46 (  56 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  71 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_32])).

tff(c_43,plain,(
    ! [C_35,A_36,B_37] :
      ( v4_relat_1(C_35,A_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_47,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_43])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(k10_relat_1(B_22,A_23),k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [B_40,A_41] :
      ( k2_xboole_0(k10_relat_1(B_40,A_41),k1_relat_1(B_40)) = k1_relat_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_26,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [B_49,A_50,C_51] :
      ( r1_tarski(k10_relat_1(B_49,A_50),C_51)
      | ~ r1_tarski(k1_relat_1(B_49),C_51)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_69,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k8_relset_1(A_42,B_43,C_44,D_45) = k10_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_72,plain,(
    ! [D_45] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_45) = k10_relat_1('#skF_4',D_45) ),
    inference(resolution,[status(thm)],[c_22,c_69])).

tff(c_20,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_73,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_20])).

tff(c_98,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_73])).

tff(c_104,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_98])).

tff(c_108,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_47,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.17  
% 1.92/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.18  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.92/1.18  
% 1.92/1.18  %Foreground sorts:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Background operators:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Foreground operators:
% 1.92/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.18  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.92/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.92/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.92/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.92/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.18  
% 1.97/1.19  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 1.97/1.19  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.97/1.19  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.97/1.19  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.97/1.19  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.97/1.19  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.97/1.19  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.97/1.19  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.97/1.19  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.19  tff(c_32, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.19  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_32])).
% 1.97/1.19  tff(c_43, plain, (![C_35, A_36, B_37]: (v4_relat_1(C_35, A_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.97/1.19  tff(c_47, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_43])).
% 1.97/1.19  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.97/1.19  tff(c_26, plain, (![B_22, A_23]: (r1_tarski(k10_relat_1(B_22, A_23), k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.19  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.19  tff(c_57, plain, (![B_40, A_41]: (k2_xboole_0(k10_relat_1(B_40, A_41), k1_relat_1(B_40))=k1_relat_1(B_40) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_26, c_4])).
% 1.97/1.19  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.19  tff(c_95, plain, (![B_49, A_50, C_51]: (r1_tarski(k10_relat_1(B_49, A_50), C_51) | ~r1_tarski(k1_relat_1(B_49), C_51) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 1.97/1.19  tff(c_69, plain, (![A_42, B_43, C_44, D_45]: (k8_relset_1(A_42, B_43, C_44, D_45)=k10_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.97/1.19  tff(c_72, plain, (![D_45]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_45)=k10_relat_1('#skF_4', D_45))), inference(resolution, [status(thm)], [c_22, c_69])).
% 1.97/1.19  tff(c_20, plain, (~r1_tarski(k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.19  tff(c_73, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_20])).
% 1.97/1.19  tff(c_98, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_95, c_73])).
% 1.97/1.19  tff(c_104, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_98])).
% 1.97/1.19  tff(c_108, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_104])).
% 1.97/1.19  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_47, c_108])).
% 1.97/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  Inference rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Ref     : 0
% 1.97/1.19  #Sup     : 18
% 1.97/1.19  #Fact    : 0
% 1.97/1.19  #Define  : 0
% 1.97/1.19  #Split   : 0
% 1.97/1.19  #Chain   : 0
% 1.97/1.19  #Close   : 0
% 1.97/1.19  
% 1.97/1.19  Ordering : KBO
% 1.97/1.19  
% 1.97/1.19  Simplification rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Subsume      : 0
% 1.97/1.19  #Demod        : 4
% 1.97/1.19  #Tautology    : 7
% 1.97/1.19  #SimpNegUnit  : 0
% 1.97/1.19  #BackRed      : 1
% 1.97/1.19  
% 1.97/1.19  #Partial instantiations: 0
% 1.97/1.19  #Strategies tried      : 1
% 1.97/1.19  
% 1.97/1.19  Timing (in seconds)
% 1.97/1.19  ----------------------
% 1.97/1.19  Preprocessing        : 0.30
% 1.97/1.19  Parsing              : 0.16
% 1.97/1.19  CNF conversion       : 0.02
% 1.97/1.19  Main loop            : 0.13
% 1.97/1.19  Inferencing          : 0.06
% 1.97/1.19  Reduction            : 0.04
% 1.97/1.19  Demodulation         : 0.03
% 1.97/1.19  BG Simplification    : 0.01
% 1.97/1.19  Subsumption          : 0.02
% 1.97/1.19  Abstraction          : 0.01
% 1.97/1.19  MUC search           : 0.00
% 1.97/1.19  Cooper               : 0.00
% 1.97/1.19  Total                : 0.46
% 1.97/1.19  Index Insertion      : 0.00
% 1.97/1.19  Index Deletion       : 0.00
% 1.97/1.19  Index Matching       : 0.00
% 1.97/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
