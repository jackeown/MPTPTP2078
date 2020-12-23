%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:49 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   59 (  71 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 100 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_53,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_59])).

tff(c_101,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_126,plain,(
    ! [A_56,B_57,C_58] :
      ( m1_subset_1(k2_relset_1(A_56,B_57,C_58),k1_zfmisc_1(B_57))
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_126])).

tff(c_144,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_139])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_144,c_6])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_166,plain,(
    k2_xboole_0(k2_relat_1('#skF_4'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_152,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_180,plain,(
    ! [C_61] :
      ( r1_tarski(k2_relat_1('#skF_4'),C_61)
      | ~ r1_tarski('#skF_2',C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_2])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k8_relat_1(A_13,B_14) = B_14
      | ~ r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_187,plain,(
    ! [C_61] :
      ( k8_relat_1(C_61,'#skF_4') = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',C_61) ) ),
    inference(resolution,[status(thm)],[c_180,c_14])).

tff(c_212,plain,(
    ! [C_66] :
      ( k8_relat_1(C_66,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',C_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_187])).

tff(c_220,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_212])).

tff(c_200,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k6_relset_1(A_62,B_63,C_64,D_65) = k8_relat_1(C_64,D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_211,plain,(
    ! [C_64] : k6_relset_1('#skF_1','#skF_2',C_64,'#skF_4') = k8_relat_1(C_64,'#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_200])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_226,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_24])).

tff(c_227,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_226])).

tff(c_284,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( r2_relset_1(A_73,B_74,C_75,C_75)
      | ~ m1_subset_1(D_76,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_301,plain,(
    ! [C_77] :
      ( r2_relset_1('#skF_1','#skF_2',C_77,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_28,c_284])).

tff(c_309,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_301])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:59:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.24  
% 2.25/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.24  %$ r2_relset_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k2_relset_1 > k8_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.25/1.24  
% 2.25/1.24  %Foreground sorts:
% 2.25/1.24  
% 2.25/1.24  
% 2.25/1.24  %Background operators:
% 2.25/1.24  
% 2.25/1.24  
% 2.25/1.24  %Foreground operators:
% 2.25/1.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.25/1.24  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.25/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.24  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.25/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.24  
% 2.25/1.26  tff(f_77, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_relset_1)).
% 2.25/1.26  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.25/1.26  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.25/1.26  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.25/1.26  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.25/1.26  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.26  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.25/1.26  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.25/1.26  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.25/1.26  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.25/1.26  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.25/1.26  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.26  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.26  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.26  tff(c_53, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.26  tff(c_59, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_53])).
% 2.25/1.26  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_59])).
% 2.25/1.26  tff(c_101, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.25/1.26  tff(c_110, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_101])).
% 2.25/1.26  tff(c_126, plain, (![A_56, B_57, C_58]: (m1_subset_1(k2_relset_1(A_56, B_57, C_58), k1_zfmisc_1(B_57)) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.25/1.26  tff(c_139, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_126])).
% 2.25/1.26  tff(c_144, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_139])).
% 2.25/1.26  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.25/1.26  tff(c_152, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_144, c_6])).
% 2.25/1.26  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.26  tff(c_166, plain, (k2_xboole_0(k2_relat_1('#skF_4'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_152, c_4])).
% 2.25/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.26  tff(c_180, plain, (![C_61]: (r1_tarski(k2_relat_1('#skF_4'), C_61) | ~r1_tarski('#skF_2', C_61))), inference(superposition, [status(thm), theory('equality')], [c_166, c_2])).
% 2.25/1.26  tff(c_14, plain, (![A_13, B_14]: (k8_relat_1(A_13, B_14)=B_14 | ~r1_tarski(k2_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.26  tff(c_187, plain, (![C_61]: (k8_relat_1(C_61, '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', C_61))), inference(resolution, [status(thm)], [c_180, c_14])).
% 2.25/1.26  tff(c_212, plain, (![C_66]: (k8_relat_1(C_66, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', C_66))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_187])).
% 2.25/1.26  tff(c_220, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_212])).
% 2.25/1.26  tff(c_200, plain, (![A_62, B_63, C_64, D_65]: (k6_relset_1(A_62, B_63, C_64, D_65)=k8_relat_1(C_64, D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.25/1.26  tff(c_211, plain, (![C_64]: (k6_relset_1('#skF_1', '#skF_2', C_64, '#skF_4')=k8_relat_1(C_64, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_200])).
% 2.25/1.26  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.26  tff(c_226, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_24])).
% 2.25/1.26  tff(c_227, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_226])).
% 2.25/1.26  tff(c_284, plain, (![A_73, B_74, C_75, D_76]: (r2_relset_1(A_73, B_74, C_75, C_75) | ~m1_subset_1(D_76, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.25/1.26  tff(c_301, plain, (![C_77]: (r2_relset_1('#skF_1', '#skF_2', C_77, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_28, c_284])).
% 2.25/1.26  tff(c_309, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_301])).
% 2.25/1.26  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227, c_309])).
% 2.25/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.26  
% 2.25/1.26  Inference rules
% 2.25/1.26  ----------------------
% 2.25/1.26  #Ref     : 0
% 2.25/1.26  #Sup     : 68
% 2.25/1.26  #Fact    : 0
% 2.25/1.26  #Define  : 0
% 2.25/1.26  #Split   : 5
% 2.25/1.26  #Chain   : 0
% 2.25/1.26  #Close   : 0
% 2.25/1.26  
% 2.25/1.26  Ordering : KBO
% 2.25/1.26  
% 2.25/1.26  Simplification rules
% 2.25/1.26  ----------------------
% 2.25/1.26  #Subsume      : 4
% 2.25/1.26  #Demod        : 10
% 2.25/1.26  #Tautology    : 22
% 2.25/1.26  #SimpNegUnit  : 1
% 2.25/1.26  #BackRed      : 1
% 2.25/1.26  
% 2.25/1.26  #Partial instantiations: 0
% 2.25/1.26  #Strategies tried      : 1
% 2.25/1.26  
% 2.25/1.26  Timing (in seconds)
% 2.25/1.26  ----------------------
% 2.25/1.26  Preprocessing        : 0.29
% 2.25/1.26  Parsing              : 0.15
% 2.25/1.26  CNF conversion       : 0.02
% 2.25/1.26  Main loop            : 0.21
% 2.25/1.26  Inferencing          : 0.08
% 2.25/1.26  Reduction            : 0.06
% 2.25/1.26  Demodulation         : 0.04
% 2.25/1.26  BG Simplification    : 0.01
% 2.25/1.26  Subsumption          : 0.04
% 2.25/1.26  Abstraction          : 0.01
% 2.25/1.26  MUC search           : 0.00
% 2.25/1.26  Cooper               : 0.00
% 2.25/1.26  Total                : 0.53
% 2.25/1.26  Index Insertion      : 0.00
% 2.25/1.26  Index Deletion       : 0.00
% 2.25/1.26  Index Matching       : 0.00
% 2.25/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
