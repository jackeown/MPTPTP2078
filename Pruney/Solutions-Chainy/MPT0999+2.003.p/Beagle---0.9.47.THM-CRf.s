%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:53 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  83 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_25,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_29,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k10_relat_1(B_5,A_4),k1_relat_1(B_5))
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [C_35,A_36,B_37] :
      ( v4_relat_1(C_35,A_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_47,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_43])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_6])).

tff(c_53,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_50])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_61,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_57])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_1')
      | ~ r1_tarski(A_42,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_74,plain,(
    ! [A_4] :
      ( r1_tarski(k10_relat_1('#skF_4',A_4),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_81,plain,(
    ! [A_4] : r1_tarski(k10_relat_1('#skF_4',A_4),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_74])).

tff(c_66,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k8_relset_1(A_38,B_39,C_40,D_41) = k10_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_69,plain,(
    ! [D_41] : k8_relset_1('#skF_1','#skF_2','#skF_4',D_41) = k10_relat_1('#skF_4',D_41) ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_18,plain,(
    ~ r1_tarski(k8_relset_1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_87,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_18])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.16  
% 1.92/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.16  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.92/1.16  
% 1.92/1.16  %Foreground sorts:
% 1.92/1.16  
% 1.92/1.16  
% 1.92/1.16  %Background operators:
% 1.92/1.16  
% 1.92/1.16  
% 1.92/1.16  %Foreground operators:
% 1.92/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.92/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.92/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.92/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.92/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.92/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.92/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.92/1.16  
% 1.92/1.18  tff(f_66, negated_conjecture, ~(![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_2)).
% 1.92/1.18  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.92/1.18  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.92/1.18  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.92/1.18  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 1.92/1.18  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 1.92/1.18  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.92/1.18  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 1.92/1.18  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.92/1.18  tff(c_25, plain, (![C_24, A_25, B_26]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.18  tff(c_29, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_25])).
% 1.92/1.18  tff(c_4, plain, (![B_5, A_4]: (r1_tarski(k10_relat_1(B_5, A_4), k1_relat_1(B_5)) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.18  tff(c_43, plain, (![C_35, A_36, B_37]: (v4_relat_1(C_35, A_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.18  tff(c_47, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_43])).
% 1.92/1.18  tff(c_6, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.18  tff(c_50, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_47, c_6])).
% 1.92/1.18  tff(c_53, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29, c_50])).
% 1.92/1.18  tff(c_8, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.18  tff(c_57, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_53, c_8])).
% 1.92/1.18  tff(c_61, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29, c_57])).
% 1.92/1.18  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.18  tff(c_70, plain, (![A_42]: (r1_tarski(A_42, '#skF_1') | ~r1_tarski(A_42, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_61, c_2])).
% 1.92/1.18  tff(c_74, plain, (![A_4]: (r1_tarski(k10_relat_1('#skF_4', A_4), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_70])).
% 1.92/1.18  tff(c_81, plain, (![A_4]: (r1_tarski(k10_relat_1('#skF_4', A_4), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_74])).
% 1.92/1.18  tff(c_66, plain, (![A_38, B_39, C_40, D_41]: (k8_relset_1(A_38, B_39, C_40, D_41)=k10_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.18  tff(c_69, plain, (![D_41]: (k8_relset_1('#skF_1', '#skF_2', '#skF_4', D_41)=k10_relat_1('#skF_4', D_41))), inference(resolution, [status(thm)], [c_20, c_66])).
% 1.92/1.18  tff(c_18, plain, (~r1_tarski(k8_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.92/1.18  tff(c_87, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_18])).
% 1.92/1.18  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_87])).
% 1.92/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.18  
% 1.92/1.18  Inference rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Ref     : 0
% 1.92/1.18  #Sup     : 14
% 1.92/1.18  #Fact    : 0
% 1.92/1.18  #Define  : 0
% 1.92/1.18  #Split   : 0
% 1.92/1.18  #Chain   : 0
% 1.92/1.18  #Close   : 0
% 1.92/1.18  
% 1.92/1.18  Ordering : KBO
% 1.92/1.18  
% 1.92/1.18  Simplification rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Subsume      : 0
% 1.92/1.18  #Demod        : 5
% 1.92/1.18  #Tautology    : 2
% 1.92/1.18  #SimpNegUnit  : 0
% 1.92/1.18  #BackRed      : 1
% 1.92/1.18  
% 1.92/1.18  #Partial instantiations: 0
% 1.92/1.18  #Strategies tried      : 1
% 1.92/1.18  
% 1.92/1.18  Timing (in seconds)
% 1.92/1.18  ----------------------
% 1.92/1.18  Preprocessing        : 0.30
% 1.92/1.18  Parsing              : 0.16
% 1.92/1.18  CNF conversion       : 0.02
% 1.92/1.18  Main loop            : 0.11
% 1.92/1.18  Inferencing          : 0.05
% 1.92/1.18  Reduction            : 0.03
% 1.92/1.18  Demodulation         : 0.03
% 1.92/1.18  BG Simplification    : 0.01
% 1.92/1.18  Subsumption          : 0.02
% 1.92/1.18  Abstraction          : 0.01
% 1.92/1.18  MUC search           : 0.00
% 1.92/1.18  Cooper               : 0.00
% 1.92/1.18  Total                : 0.44
% 1.92/1.18  Index Insertion      : 0.00
% 1.92/1.18  Index Deletion       : 0.00
% 1.92/1.18  Index Matching       : 0.00
% 1.92/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
