%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:02 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   51 (  63 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  78 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_59,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_59])).

tff(c_116,plain,(
    ! [C_51,B_52,A_53] :
      ( v5_relat_1(C_51,B_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_146,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_137])).

tff(c_172,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k1_relset_1(A_76,B_77,C_78),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_194,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_172])).

tff(c_201,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_194])).

tff(c_8,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_205,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_201,c_8])).

tff(c_16,plain,(
    ! [A_13] :
      ( k2_xboole_0(k1_relat_1(A_13),k2_relat_1(A_13)) = k3_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_165,plain,(
    ! [A_72,C_73,B_74,D_75] :
      ( r1_tarski(k2_xboole_0(A_72,C_73),k2_xboole_0(B_74,D_75))
      | ~ r1_tarski(C_73,D_75)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_298,plain,(
    ! [A_108,B_109,D_110] :
      ( r1_tarski(k3_relat_1(A_108),k2_xboole_0(B_109,D_110))
      | ~ r1_tarski(k2_relat_1(A_108),D_110)
      | ~ r1_tarski(k1_relat_1(A_108),B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_165])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_301,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_298,c_28])).

tff(c_307,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_205,c_301])).

tff(c_310,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_307])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_125,c_310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.27  
% 2.14/1.27  %Foreground sorts:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Background operators:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Foreground operators:
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.27  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.14/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.14/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.14/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.14/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.27  
% 2.14/1.28  tff(f_72, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 2.14/1.28  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.14/1.28  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.14/1.28  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.14/1.28  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.14/1.28  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.14/1.28  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.14/1.28  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.14/1.28  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 2.14/1.28  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.14/1.28  tff(c_59, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.28  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_59])).
% 2.14/1.28  tff(c_116, plain, (![C_51, B_52, A_53]: (v5_relat_1(C_51, B_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.14/1.28  tff(c_125, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_116])).
% 2.14/1.28  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.28  tff(c_137, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.14/1.28  tff(c_146, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_137])).
% 2.14/1.28  tff(c_172, plain, (![A_76, B_77, C_78]: (m1_subset_1(k1_relset_1(A_76, B_77, C_78), k1_zfmisc_1(A_76)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.28  tff(c_194, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_146, c_172])).
% 2.14/1.28  tff(c_201, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_194])).
% 2.14/1.28  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.28  tff(c_205, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_201, c_8])).
% 2.14/1.28  tff(c_16, plain, (![A_13]: (k2_xboole_0(k1_relat_1(A_13), k2_relat_1(A_13))=k3_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.28  tff(c_165, plain, (![A_72, C_73, B_74, D_75]: (r1_tarski(k2_xboole_0(A_72, C_73), k2_xboole_0(B_74, D_75)) | ~r1_tarski(C_73, D_75) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.28  tff(c_298, plain, (![A_108, B_109, D_110]: (r1_tarski(k3_relat_1(A_108), k2_xboole_0(B_109, D_110)) | ~r1_tarski(k2_relat_1(A_108), D_110) | ~r1_tarski(k1_relat_1(A_108), B_109) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_16, c_165])).
% 2.14/1.28  tff(c_28, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.14/1.28  tff(c_301, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_298, c_28])).
% 2.14/1.28  tff(c_307, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_205, c_301])).
% 2.14/1.28  tff(c_310, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_307])).
% 2.14/1.28  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_125, c_310])).
% 2.14/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  Inference rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Ref     : 0
% 2.14/1.28  #Sup     : 57
% 2.14/1.28  #Fact    : 0
% 2.14/1.28  #Define  : 0
% 2.14/1.28  #Split   : 0
% 2.14/1.28  #Chain   : 0
% 2.14/1.28  #Close   : 0
% 2.14/1.28  
% 2.14/1.28  Ordering : KBO
% 2.14/1.28  
% 2.14/1.28  Simplification rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Subsume      : 2
% 2.14/1.28  #Demod        : 13
% 2.14/1.28  #Tautology    : 16
% 2.14/1.28  #SimpNegUnit  : 0
% 2.14/1.28  #BackRed      : 0
% 2.14/1.28  
% 2.14/1.28  #Partial instantiations: 0
% 2.14/1.28  #Strategies tried      : 1
% 2.14/1.28  
% 2.14/1.28  Timing (in seconds)
% 2.14/1.28  ----------------------
% 2.14/1.28  Preprocessing        : 0.30
% 2.14/1.28  Parsing              : 0.16
% 2.14/1.29  CNF conversion       : 0.02
% 2.14/1.29  Main loop            : 0.21
% 2.14/1.29  Inferencing          : 0.09
% 2.14/1.29  Reduction            : 0.06
% 2.14/1.29  Demodulation         : 0.04
% 2.14/1.29  BG Simplification    : 0.01
% 2.14/1.29  Subsumption          : 0.03
% 2.14/1.29  Abstraction          : 0.01
% 2.14/1.29  MUC search           : 0.00
% 2.14/1.29  Cooper               : 0.00
% 2.14/1.29  Total                : 0.53
% 2.14/1.29  Index Insertion      : 0.00
% 2.14/1.29  Index Deletion       : 0.00
% 2.14/1.29  Index Matching       : 0.00
% 2.14/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
