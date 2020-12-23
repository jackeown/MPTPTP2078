%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:15 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   69 ( 118 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    ! [A_22,B_23,C_24] :
      ( k2_relset_1(A_22,B_23,C_24) = k2_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_102,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_relset_1(A_37,B_38,C_39) = k1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_55,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_107,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_55])).

tff(c_45,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_45])).

tff(c_22,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(k1_relat_1(A_29),k1_relat_1(B_30))
      | ~ r1_tarski(A_29,B_30)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_81,plain,(
    ! [A_4,B_30] :
      ( r1_tarski(A_4,k1_relat_1(B_30))
      | ~ r1_tarski(k6_relat_1(A_4),B_30)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_78])).

tff(c_112,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,k1_relat_1(B_41))
      | ~ r1_tarski(k6_relat_1(A_40),B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_81])).

tff(c_115,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_112])).

tff(c_118,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_115])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_118])).

tff(c_121,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_134,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_121])).

tff(c_8,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_123,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(k2_relat_1(A_42),k2_relat_1(B_43))
      | ~ r1_tarski(A_42,B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_126,plain,(
    ! [A_4,B_43] :
      ( r1_tarski(A_4,k2_relat_1(B_43))
      | ~ r1_tarski(k6_relat_1(A_4),B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_123])).

tff(c_139,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,k2_relat_1(B_45))
      | ~ r1_tarski(k6_relat_1(A_44),B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_126])).

tff(c_142,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_139])).

tff(c_145,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:08:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.57  
% 2.26/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.58  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.26/1.58  
% 2.26/1.58  %Foreground sorts:
% 2.26/1.58  
% 2.26/1.58  
% 2.26/1.58  %Background operators:
% 2.26/1.58  
% 2.26/1.58  
% 2.26/1.58  %Foreground operators:
% 2.26/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.26/1.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.26/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.58  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.26/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.58  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.26/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.58  
% 2.26/1.60  tff(f_65, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.26/1.60  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.26/1.60  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.26/1.60  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.26/1.60  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 2.26/1.60  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.26/1.60  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.26/1.60  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.60  tff(c_50, plain, (![A_22, B_23, C_24]: (k2_relset_1(A_22, B_23, C_24)=k2_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.60  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_50])).
% 2.26/1.60  tff(c_102, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.26/1.60  tff(c_106, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_102])).
% 2.26/1.60  tff(c_20, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.60  tff(c_55, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_20])).
% 2.26/1.60  tff(c_107, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_55])).
% 2.26/1.60  tff(c_45, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.26/1.60  tff(c_49, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_45])).
% 2.26/1.60  tff(c_22, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.26/1.60  tff(c_10, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.26/1.60  tff(c_6, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.60  tff(c_78, plain, (![A_29, B_30]: (r1_tarski(k1_relat_1(A_29), k1_relat_1(B_30)) | ~r1_tarski(A_29, B_30) | ~v1_relat_1(B_30) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.60  tff(c_81, plain, (![A_4, B_30]: (r1_tarski(A_4, k1_relat_1(B_30)) | ~r1_tarski(k6_relat_1(A_4), B_30) | ~v1_relat_1(B_30) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_78])).
% 2.26/1.60  tff(c_112, plain, (![A_40, B_41]: (r1_tarski(A_40, k1_relat_1(B_41)) | ~r1_tarski(k6_relat_1(A_40), B_41) | ~v1_relat_1(B_41))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_81])).
% 2.26/1.60  tff(c_115, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_112])).
% 2.26/1.60  tff(c_118, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_115])).
% 2.26/1.60  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_118])).
% 2.26/1.60  tff(c_121, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_20])).
% 2.26/1.60  tff(c_134, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_121])).
% 2.26/1.60  tff(c_8, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.60  tff(c_123, plain, (![A_42, B_43]: (r1_tarski(k2_relat_1(A_42), k2_relat_1(B_43)) | ~r1_tarski(A_42, B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.26/1.60  tff(c_126, plain, (![A_4, B_43]: (r1_tarski(A_4, k2_relat_1(B_43)) | ~r1_tarski(k6_relat_1(A_4), B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_123])).
% 2.26/1.60  tff(c_139, plain, (![A_44, B_45]: (r1_tarski(A_44, k2_relat_1(B_45)) | ~r1_tarski(k6_relat_1(A_44), B_45) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_126])).
% 2.26/1.60  tff(c_142, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_139])).
% 2.26/1.60  tff(c_145, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_142])).
% 2.26/1.60  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_145])).
% 2.26/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.60  
% 2.26/1.60  Inference rules
% 2.26/1.60  ----------------------
% 2.26/1.60  #Ref     : 0
% 2.26/1.60  #Sup     : 24
% 2.26/1.60  #Fact    : 0
% 2.26/1.60  #Define  : 0
% 2.26/1.60  #Split   : 1
% 2.26/1.60  #Chain   : 0
% 2.26/1.60  #Close   : 0
% 2.26/1.60  
% 2.26/1.60  Ordering : KBO
% 2.26/1.60  
% 2.26/1.60  Simplification rules
% 2.26/1.60  ----------------------
% 2.26/1.60  #Subsume      : 1
% 2.26/1.60  #Demod        : 13
% 2.26/1.60  #Tautology    : 10
% 2.26/1.60  #SimpNegUnit  : 2
% 2.26/1.60  #BackRed      : 2
% 2.26/1.60  
% 2.26/1.60  #Partial instantiations: 0
% 2.26/1.60  #Strategies tried      : 1
% 2.26/1.60  
% 2.26/1.60  Timing (in seconds)
% 2.26/1.60  ----------------------
% 2.26/1.60  Preprocessing        : 0.45
% 2.26/1.60  Parsing              : 0.24
% 2.26/1.60  CNF conversion       : 0.03
% 2.26/1.60  Main loop            : 0.24
% 2.26/1.60  Inferencing          : 0.09
% 2.26/1.60  Reduction            : 0.08
% 2.26/1.60  Demodulation         : 0.06
% 2.26/1.60  BG Simplification    : 0.02
% 2.26/1.60  Subsumption          : 0.03
% 2.26/1.60  Abstraction          : 0.02
% 2.26/1.60  MUC search           : 0.00
% 2.26/1.60  Cooper               : 0.00
% 2.26/1.60  Total                : 0.75
% 2.26/1.60  Index Insertion      : 0.00
% 2.26/1.61  Index Deletion       : 0.00
% 2.26/1.61  Index Matching       : 0.00
% 2.26/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
