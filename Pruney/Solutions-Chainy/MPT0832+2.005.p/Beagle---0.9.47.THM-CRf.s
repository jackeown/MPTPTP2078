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
% DateTime   : Thu Dec  3 10:07:41 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 106 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 160 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => m1_subset_1(k6_relset_1(C,A,B,D),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k6_relset_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [A_41,B_42,C_43,D_44] :
      ( k6_relset_1(A_41,B_42,C_43,D_44) = k8_relat_1(C_43,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_51,plain,(
    ! [C_43] : k6_relset_1('#skF_3','#skF_1',C_43,'#skF_4') = k8_relat_1(C_43,'#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_48])).

tff(c_86,plain,(
    ! [A_52,B_53,C_54,D_55] :
      ( m1_subset_1(k6_relset_1(A_52,B_53,C_54,D_55),k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [C_43] :
      ( m1_subset_1(k8_relat_1(C_43,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_86])).

tff(c_107,plain,(
    ! [C_56] : m1_subset_1(k8_relat_1(C_56,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_100])).

tff(c_10,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ! [C_56] : v1_relat_1(k8_relat_1(C_56,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_107,c_10])).

tff(c_14,plain,(
    ! [C_12,A_10,B_11] :
      ( v4_relat_1(C_12,A_10)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [C_56] : v4_relat_1(k8_relat_1(C_56,'#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_107,c_14])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_31,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_27])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_5,B_6)),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k8_relat_1(A_3,B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [C_46,A_47,B_48] :
      ( m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ r1_tarski(k2_relat_1(C_46),B_48)
      | ~ r1_tarski(k1_relat_1(C_46),A_47)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ~ m1_subset_1(k6_relset_1('#skF_3','#skF_1','#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ~ m1_subset_1(k8_relat_1('#skF_2','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_22])).

tff(c_77,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_52])).

tff(c_123,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_126,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_126])).

tff(c_131,plain,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_152,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_155,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_155])).

tff(c_160,plain,(
    ~ r1_tarski(k1_relat_1(k8_relat_1('#skF_2','#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_164,plain,
    ( ~ v4_relat_1(k8_relat_1('#skF_2','#skF_4'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_121,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.20  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.93/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.93/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.20  
% 2.04/1.22  tff(f_70, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => m1_subset_1(k6_relset_1(C, A, B, D), k1_zfmisc_1(k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_relset_1)).
% 2.04/1.22  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.04/1.22  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k6_relset_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relset_1)).
% 2.04/1.22  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.04/1.22  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.04/1.22  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.04/1.22  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.04/1.22  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.04/1.22  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.04/1.22  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.22  tff(c_48, plain, (![A_41, B_42, C_43, D_44]: (k6_relset_1(A_41, B_42, C_43, D_44)=k8_relat_1(C_43, D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.04/1.22  tff(c_51, plain, (![C_43]: (k6_relset_1('#skF_3', '#skF_1', C_43, '#skF_4')=k8_relat_1(C_43, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_48])).
% 2.04/1.22  tff(c_86, plain, (![A_52, B_53, C_54, D_55]: (m1_subset_1(k6_relset_1(A_52, B_53, C_54, D_55), k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.22  tff(c_100, plain, (![C_43]: (m1_subset_1(k8_relat_1(C_43, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_51, c_86])).
% 2.04/1.22  tff(c_107, plain, (![C_56]: (m1_subset_1(k8_relat_1(C_56, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_100])).
% 2.04/1.22  tff(c_10, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.22  tff(c_122, plain, (![C_56]: (v1_relat_1(k8_relat_1(C_56, '#skF_4')))), inference(resolution, [status(thm)], [c_107, c_10])).
% 2.04/1.22  tff(c_14, plain, (![C_12, A_10, B_11]: (v4_relat_1(C_12, A_10) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.22  tff(c_121, plain, (![C_56]: (v4_relat_1(k8_relat_1(C_56, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_107, c_14])).
% 2.04/1.22  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.22  tff(c_27, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.22  tff(c_31, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_27])).
% 2.04/1.22  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k2_relat_1(k8_relat_1(A_5, B_6)), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.22  tff(c_6, plain, (![A_3, B_4]: (v1_relat_1(k8_relat_1(A_3, B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.22  tff(c_62, plain, (![C_46, A_47, B_48]: (m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~r1_tarski(k2_relat_1(C_46), B_48) | ~r1_tarski(k1_relat_1(C_46), A_47) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.04/1.22  tff(c_22, plain, (~m1_subset_1(k6_relset_1('#skF_3', '#skF_1', '#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.04/1.22  tff(c_52, plain, (~m1_subset_1(k8_relat_1('#skF_2', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_22])).
% 2.04/1.22  tff(c_77, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2') | ~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_52])).
% 2.04/1.22  tff(c_123, plain, (~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_77])).
% 2.04/1.22  tff(c_126, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_123])).
% 2.04/1.22  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_126])).
% 2.04/1.22  tff(c_131, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3') | ~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitRight, [status(thm)], [c_77])).
% 2.04/1.22  tff(c_152, plain, (~r1_tarski(k2_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_131])).
% 2.04/1.22  tff(c_155, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_152])).
% 2.04/1.22  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_155])).
% 2.04/1.22  tff(c_160, plain, (~r1_tarski(k1_relat_1(k8_relat_1('#skF_2', '#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_131])).
% 2.04/1.22  tff(c_164, plain, (~v4_relat_1(k8_relat_1('#skF_2', '#skF_4'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_160])).
% 2.04/1.22  tff(c_168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_121, c_164])).
% 2.04/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.22  
% 2.04/1.22  Inference rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Ref     : 0
% 2.04/1.22  #Sup     : 29
% 2.04/1.22  #Fact    : 0
% 2.04/1.22  #Define  : 0
% 2.04/1.22  #Split   : 2
% 2.04/1.22  #Chain   : 0
% 2.04/1.22  #Close   : 0
% 2.04/1.22  
% 2.04/1.22  Ordering : KBO
% 2.04/1.22  
% 2.04/1.22  Simplification rules
% 2.04/1.22  ----------------------
% 2.04/1.22  #Subsume      : 1
% 2.04/1.22  #Demod        : 9
% 2.04/1.22  #Tautology    : 6
% 2.04/1.22  #SimpNegUnit  : 0
% 2.04/1.22  #BackRed      : 1
% 2.04/1.22  
% 2.04/1.22  #Partial instantiations: 0
% 2.04/1.22  #Strategies tried      : 1
% 2.04/1.22  
% 2.04/1.22  Timing (in seconds)
% 2.04/1.22  ----------------------
% 2.04/1.22  Preprocessing        : 0.29
% 2.04/1.22  Parsing              : 0.16
% 2.04/1.22  CNF conversion       : 0.02
% 2.04/1.22  Main loop            : 0.16
% 2.04/1.22  Inferencing          : 0.06
% 2.04/1.22  Reduction            : 0.05
% 2.04/1.22  Demodulation         : 0.03
% 2.04/1.22  BG Simplification    : 0.01
% 2.04/1.22  Subsumption          : 0.02
% 2.04/1.22  Abstraction          : 0.01
% 2.04/1.22  MUC search           : 0.00
% 2.04/1.22  Cooper               : 0.00
% 2.04/1.22  Total                : 0.48
% 2.04/1.22  Index Insertion      : 0.00
% 2.04/1.22  Index Deletion       : 0.00
% 2.04/1.22  Index Matching       : 0.00
% 2.04/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
