%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:47 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   58 (  82 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 133 expanded)
%              Number of equality atoms :   15 (  15 expanded)
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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(B,C)
         => r2_relset_1(A,B,k6_relset_1(A,B,C,D),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_relset_1)).

tff(f_80,axiom,(
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

tff(f_68,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k6_relset_1(A,B,C,D) = k8_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_97,plain,(
    ! [A_50,B_51,D_52] :
      ( r2_relset_1(A_50,B_51,D_52,D_52)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_97])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_61,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_58])).

tff(c_62,plain,(
    ! [C_37,B_38,A_39] :
      ( v5_relat_1(C_37,B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_39,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_87,plain,(
    ! [A_48,B_49] :
      ( k8_relat_1(A_48,B_49) = B_49
      | ~ r1_tarski(k2_relat_1(B_49),A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,(
    ! [A_54,B_55] :
      ( k8_relat_1(A_54,B_55) = B_55
      | ~ v5_relat_1(B_55,A_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_12,c_87])).

tff(c_120,plain,
    ( k8_relat_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_114])).

tff(c_124,plain,(
    k8_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_120])).

tff(c_150,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(k8_relat_1(A_58,C_59),k8_relat_1(B_60,C_59))
      | ~ r1_tarski(A_58,B_60)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_155,plain,(
    ! [B_60] :
      ( r1_tarski('#skF_4',k8_relat_1(B_60,'#skF_4'))
      | ~ r1_tarski('#skF_2',B_60)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_150])).

tff(c_170,plain,(
    ! [B_61] :
      ( r1_tarski('#skF_4',k8_relat_1(B_61,'#skF_4'))
      | ~ r1_tarski('#skF_2',B_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_155])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_10,B_11] :
      ( k8_relat_1(A_10,B_11) = B_11
      | ~ r1_tarski(B_11,k8_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_41])).

tff(c_173,plain,(
    ! [B_61] :
      ( k8_relat_1(B_61,'#skF_4') = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_61) ) ),
    inference(resolution,[status(thm)],[c_170,c_48])).

tff(c_191,plain,(
    ! [B_62] :
      ( k8_relat_1(B_62,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_2',B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_173])).

tff(c_201,plain,(
    k8_relat_1('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_191])).

tff(c_344,plain,(
    ! [A_70,B_71,C_72,D_73] :
      ( k6_relset_1(A_70,B_71,C_72,D_73) = k8_relat_1(C_72,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_347,plain,(
    ! [C_72] : k6_relset_1('#skF_1','#skF_2',C_72,'#skF_4') = k8_relat_1(C_72,'#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_344])).

tff(c_32,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k6_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_348,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_32])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_201,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.31  
% 2.35/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.31  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k6_relset_1 > k8_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.31  
% 2.35/1.31  %Foreground sorts:
% 2.35/1.31  
% 2.35/1.31  
% 2.35/1.31  %Background operators:
% 2.35/1.31  
% 2.35/1.31  
% 2.35/1.31  %Foreground operators:
% 2.35/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.35/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.31  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.35/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.35/1.31  tff(k6_relset_1, type, k6_relset_1: ($i * $i * $i * $i) > $i).
% 2.35/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.35/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.35/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.35/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.35/1.31  
% 2.35/1.32  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(B, C) => r2_relset_1(A, B, k6_relset_1(A, B, C, D), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_relset_1)).
% 2.35/1.32  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.35/1.32  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.35/1.32  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.35/1.32  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.35/1.32  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.35/1.32  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.35/1.32  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t131_relat_1)).
% 2.35/1.32  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.35/1.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.35/1.32  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k6_relset_1(A, B, C, D) = k8_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_relset_1)).
% 2.35/1.32  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.35/1.32  tff(c_97, plain, (![A_50, B_51, D_52]: (r2_relset_1(A_50, B_51, D_52, D_52) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.35/1.32  tff(c_100, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_97])).
% 2.35/1.32  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.35/1.32  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.35/1.32  tff(c_55, plain, (![B_35, A_36]: (v1_relat_1(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.35/1.32  tff(c_58, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_55])).
% 2.35/1.32  tff(c_61, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_58])).
% 2.35/1.32  tff(c_62, plain, (![C_37, B_38, A_39]: (v5_relat_1(C_37, B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_39, B_38))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.35/1.32  tff(c_66, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_62])).
% 2.35/1.32  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.35/1.32  tff(c_87, plain, (![A_48, B_49]: (k8_relat_1(A_48, B_49)=B_49 | ~r1_tarski(k2_relat_1(B_49), A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.32  tff(c_114, plain, (![A_54, B_55]: (k8_relat_1(A_54, B_55)=B_55 | ~v5_relat_1(B_55, A_54) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_12, c_87])).
% 2.35/1.32  tff(c_120, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_114])).
% 2.35/1.32  tff(c_124, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_120])).
% 2.35/1.32  tff(c_150, plain, (![A_58, C_59, B_60]: (r1_tarski(k8_relat_1(A_58, C_59), k8_relat_1(B_60, C_59)) | ~r1_tarski(A_58, B_60) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.35/1.32  tff(c_155, plain, (![B_60]: (r1_tarski('#skF_4', k8_relat_1(B_60, '#skF_4')) | ~r1_tarski('#skF_2', B_60) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_150])).
% 2.35/1.32  tff(c_170, plain, (![B_61]: (r1_tarski('#skF_4', k8_relat_1(B_61, '#skF_4')) | ~r1_tarski('#skF_2', B_61))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_155])).
% 2.35/1.32  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.35/1.32  tff(c_41, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.32  tff(c_48, plain, (![A_10, B_11]: (k8_relat_1(A_10, B_11)=B_11 | ~r1_tarski(B_11, k8_relat_1(A_10, B_11)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_16, c_41])).
% 2.35/1.32  tff(c_173, plain, (![B_61]: (k8_relat_1(B_61, '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_61))), inference(resolution, [status(thm)], [c_170, c_48])).
% 2.35/1.32  tff(c_191, plain, (![B_62]: (k8_relat_1(B_62, '#skF_4')='#skF_4' | ~r1_tarski('#skF_2', B_62))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_173])).
% 2.35/1.32  tff(c_201, plain, (k8_relat_1('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_191])).
% 2.35/1.32  tff(c_344, plain, (![A_70, B_71, C_72, D_73]: (k6_relset_1(A_70, B_71, C_72, D_73)=k8_relat_1(C_72, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.35/1.32  tff(c_347, plain, (![C_72]: (k6_relset_1('#skF_1', '#skF_2', C_72, '#skF_4')=k8_relat_1(C_72, '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_344])).
% 2.35/1.32  tff(c_32, plain, (~r2_relset_1('#skF_1', '#skF_2', k6_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.35/1.32  tff(c_348, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_32])).
% 2.35/1.32  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_201, c_348])).
% 2.35/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.32  
% 2.35/1.32  Inference rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Ref     : 0
% 2.35/1.32  #Sup     : 64
% 2.35/1.32  #Fact    : 0
% 2.35/1.32  #Define  : 0
% 2.35/1.32  #Split   : 1
% 2.35/1.32  #Chain   : 0
% 2.35/1.32  #Close   : 0
% 2.35/1.32  
% 2.35/1.32  Ordering : KBO
% 2.35/1.32  
% 2.35/1.32  Simplification rules
% 2.35/1.32  ----------------------
% 2.35/1.32  #Subsume      : 8
% 2.35/1.32  #Demod        : 56
% 2.35/1.32  #Tautology    : 28
% 2.35/1.32  #SimpNegUnit  : 0
% 2.35/1.32  #BackRed      : 1
% 2.35/1.32  
% 2.35/1.32  #Partial instantiations: 0
% 2.35/1.32  #Strategies tried      : 1
% 2.35/1.32  
% 2.35/1.32  Timing (in seconds)
% 2.35/1.32  ----------------------
% 2.35/1.33  Preprocessing        : 0.31
% 2.35/1.33  Parsing              : 0.17
% 2.35/1.33  CNF conversion       : 0.02
% 2.35/1.33  Main loop            : 0.22
% 2.35/1.33  Inferencing          : 0.08
% 2.35/1.33  Reduction            : 0.07
% 2.35/1.33  Demodulation         : 0.05
% 2.35/1.33  BG Simplification    : 0.01
% 2.35/1.33  Subsumption          : 0.04
% 2.35/1.33  Abstraction          : 0.01
% 2.35/1.33  MUC search           : 0.00
% 2.35/1.33  Cooper               : 0.00
% 2.35/1.33  Total                : 0.55
% 2.35/1.33  Index Insertion      : 0.00
% 2.35/1.33  Index Deletion       : 0.00
% 2.35/1.33  Index Matching       : 0.00
% 2.35/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
