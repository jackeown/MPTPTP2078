%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:47 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 117 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_relset_1,type,(
    k6_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_118,plain,(
    ! [A_49,B_50,D_51] :
      ( r2_relset_1(A_49,B_50,D_51,D_51)
      | ~ m1_subset_1(D_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_118])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_33])).

tff(c_55,plain,(
    ! [C_35,B_36,A_37] :
      ( v5_relat_1(C_35,B_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_37,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_42,plain,(
    ! [B_32,A_33] :
      ( r1_tarski(k2_relat_1(B_32),A_33)
      | ~ v5_relat_1(B_32,A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_37,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(A_28,C_29)
      | ~ r1_tarski(B_30,C_29)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_3')
      | ~ r1_tarski(A_28,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_49,plain,(
    ! [B_32] :
      ( r1_tarski(k2_relat_1(B_32),'#skF_3')
      | ~ v5_relat_1(B_32,'#skF_2')
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_42,c_40])).

tff(c_65,plain,(
    ! [B_41,A_42] :
      ( v5_relat_1(B_41,A_42)
      | ~ r1_tarski(k2_relat_1(B_41),A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_83,plain,(
    ! [B_45] :
      ( v5_relat_1(B_45,'#skF_3')
      | ~ v5_relat_1(B_45,'#skF_2')
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_49,c_65])).

tff(c_86,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_83])).

tff(c_89,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_86])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_74,plain,(
    ! [A_43,B_44] :
      ( k8_relat_1(A_43,B_44) = B_44
      | ~ r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90,plain,(
    ! [A_46,B_47] :
      ( k8_relat_1(A_46,B_47) = B_47
      | ~ v5_relat_1(B_47,A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_93,plain,
    ( k8_relat_1('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_89,c_90])).

tff(c_99,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93])).

tff(c_127,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k6_relset_1(A_55,B_56,C_57,D_58) = k8_relat_1(C_57,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    ! [C_57] : k6_relset_1('#skF_1','#skF_2',C_57,'#skF_4') = k8_relat_1(C_57,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_127])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_131,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_24])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_99,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.18  
% 2.09/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.18  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.18  
% 2.09/1.18  %Foreground sorts:
% 2.09/1.18  
% 2.09/1.18  
% 2.09/1.18  %Background operators:
% 2.09/1.18  
% 2.09/1.18  
% 2.09/1.18  %Foreground operators:
% 2.09/1.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.09/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.18  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.09/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.18  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.09/1.18  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.18  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.18  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.09/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.18  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.09/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.18  
% 2.09/1.19  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.09/1.19  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.09/1.19  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.09/1.19  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.09/1.19  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.09/1.19  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.09/1.19  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.09/1.19  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.09/1.19  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.09/1.19  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.19  tff(c_118, plain, (![A_49, B_50, D_51]: (r2_relset_1(A_49, B_50, D_51, D_51) | ~m1_subset_1(D_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.19  tff(c_121, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_118])).
% 2.09/1.19  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.19  tff(c_30, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.09/1.19  tff(c_33, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_30])).
% 2.09/1.19  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_33])).
% 2.09/1.19  tff(c_55, plain, (![C_35, B_36, A_37]: (v5_relat_1(C_35, B_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_37, B_36))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.19  tff(c_59, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_55])).
% 2.09/1.19  tff(c_42, plain, (![B_32, A_33]: (r1_tarski(k2_relat_1(B_32), A_33) | ~v5_relat_1(B_32, A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.19  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.19  tff(c_37, plain, (![A_28, C_29, B_30]: (r1_tarski(A_28, C_29) | ~r1_tarski(B_30, C_29) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.19  tff(c_40, plain, (![A_28]: (r1_tarski(A_28, '#skF_3') | ~r1_tarski(A_28, '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_37])).
% 2.09/1.19  tff(c_49, plain, (![B_32]: (r1_tarski(k2_relat_1(B_32), '#skF_3') | ~v5_relat_1(B_32, '#skF_2') | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_42, c_40])).
% 2.09/1.19  tff(c_65, plain, (![B_41, A_42]: (v5_relat_1(B_41, A_42) | ~r1_tarski(k2_relat_1(B_41), A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.19  tff(c_83, plain, (![B_45]: (v5_relat_1(B_45, '#skF_3') | ~v5_relat_1(B_45, '#skF_2') | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_49, c_65])).
% 2.09/1.19  tff(c_86, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_59, c_83])).
% 2.09/1.19  tff(c_89, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_86])).
% 2.09/1.19  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.09/1.19  tff(c_74, plain, (![A_43, B_44]: (k8_relat_1(A_43, B_44)=B_44 | ~r1_tarski(k2_relat_1(B_44), A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.19  tff(c_90, plain, (![A_46, B_47]: (k8_relat_1(A_46, B_47)=B_47 | ~v5_relat_1(B_47, A_46) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_8, c_74])).
% 2.09/1.19  tff(c_93, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_89, c_90])).
% 2.09/1.19  tff(c_99, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_93])).
% 2.09/1.19  tff(c_127, plain, (![A_55, B_56, C_57, D_58]: (k6_relset_1(A_55, B_56, C_57, D_58)=k8_relat_1(C_57, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.19  tff(c_130, plain, (![C_57]: (k6_relset_1('#skF_1', '#skF_2', C_57, '#skF_4')=k8_relat_1(C_57, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_127])).
% 2.09/1.19  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.09/1.19  tff(c_131, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_24])).
% 2.09/1.19  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_99, c_131])).
% 2.09/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.19  
% 2.09/1.19  Inference rules
% 2.09/1.19  ----------------------
% 2.09/1.19  #Ref     : 0
% 2.09/1.19  #Sup     : 22
% 2.09/1.19  #Fact    : 0
% 2.09/1.19  #Define  : 0
% 2.09/1.19  #Split   : 0
% 2.09/1.19  #Chain   : 0
% 2.09/1.19  #Close   : 0
% 2.09/1.19  
% 2.09/1.19  Ordering : KBO
% 2.09/1.19  
% 2.09/1.19  Simplification rules
% 2.09/1.20  ----------------------
% 2.09/1.20  #Subsume      : 0
% 2.09/1.20  #Demod        : 9
% 2.09/1.20  #Tautology    : 6
% 2.09/1.20  #SimpNegUnit  : 0
% 2.09/1.20  #BackRed      : 1
% 2.09/1.20  
% 2.09/1.20  #Partial instantiations: 0
% 2.09/1.20  #Strategies tried      : 1
% 2.09/1.20  
% 2.09/1.20  Timing (in seconds)
% 2.09/1.20  ----------------------
% 2.09/1.20  Preprocessing        : 0.29
% 2.09/1.20  Parsing              : 0.15
% 2.09/1.20  CNF conversion       : 0.02
% 2.09/1.20  Main loop            : 0.13
% 2.09/1.20  Inferencing          : 0.05
% 2.09/1.20  Reduction            : 0.04
% 2.09/1.20  Demodulation         : 0.03
% 2.09/1.20  BG Simplification    : 0.01
% 2.09/1.20  Subsumption          : 0.02
% 2.09/1.20  Abstraction          : 0.01
% 2.09/1.20  MUC search           : 0.00
% 2.09/1.20  Cooper               : 0.00
% 2.09/1.20  Total                : 0.46
% 2.09/1.20  Index Insertion      : 0.00
% 2.09/1.20  Index Deletion       : 0.00
% 2.09/1.20  Index Matching       : 0.00
% 2.09/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
