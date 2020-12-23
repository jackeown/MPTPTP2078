%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:28 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 150 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 248 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_45,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_35])).

tff(c_148,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_161,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43,c_148])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_109,plain,(
    ! [A_4,B_49,A_50] :
      ( v5_relat_1(A_4,B_49)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_50,B_49)) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_178,plain,(
    ! [A_61] :
      ( v5_relat_1(A_61,'#skF_3')
      | ~ r1_tarski(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_161,c_109])).

tff(c_53,plain,(
    ! [A_4,A_37,B_38] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_37,B_38)) ) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_182,plain,(
    ! [A_62] :
      ( v1_relat_1(A_62)
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_161,c_53])).

tff(c_194,plain,(
    ! [A_13] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_13))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_182])).

tff(c_199,plain,(
    ! [A_13] : v1_relat_1(k7_relat_1('#skF_4',A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_194])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_459,plain,(
    ! [C_135,A_136,B_137] :
      ( m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137)))
      | ~ r1_tarski(k2_relat_1(C_135),B_137)
      | ~ r1_tarski(k1_relat_1(C_135),A_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_386,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k5_relset_1(A_116,B_117,C_118,D_119) = k7_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_393,plain,(
    ! [D_119] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_119) = k7_relat_1('#skF_4',D_119) ),
    inference(resolution,[status(thm)],[c_32,c_386])).

tff(c_30,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_395,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_30])).

tff(c_462,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_459,c_395])).

tff(c_479,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_462])).

tff(c_506,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_479])).

tff(c_509,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_506])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_509])).

tff(c_514,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_479])).

tff(c_518,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_514])).

tff(c_521,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_518])).

tff(c_531,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_178,c_521])).

tff(c_534,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_531])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.35  
% 2.67/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.36  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.67/1.36  
% 2.67/1.36  %Foreground sorts:
% 2.67/1.36  
% 2.67/1.36  
% 2.67/1.36  %Background operators:
% 2.67/1.36  
% 2.67/1.36  
% 2.67/1.36  %Foreground operators:
% 2.67/1.36  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.67/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.67/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.67/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.67/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.36  
% 2.67/1.37  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.67/1.37  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.67/1.37  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.67/1.37  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.67/1.37  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.67/1.37  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.67/1.37  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.67/1.37  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.67/1.37  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.67/1.37  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.67/1.37  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.67/1.37  tff(c_45, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.37  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_45])).
% 2.67/1.37  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.37  tff(c_35, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.37  tff(c_43, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_35])).
% 2.67/1.37  tff(c_148, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.37  tff(c_161, plain, (![A_61]: (r1_tarski(A_61, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_61, '#skF_4'))), inference(resolution, [status(thm)], [c_43, c_148])).
% 2.67/1.37  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.37  tff(c_101, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.67/1.37  tff(c_109, plain, (![A_4, B_49, A_50]: (v5_relat_1(A_4, B_49) | ~r1_tarski(A_4, k2_zfmisc_1(A_50, B_49)))), inference(resolution, [status(thm)], [c_6, c_101])).
% 2.67/1.37  tff(c_178, plain, (![A_61]: (v5_relat_1(A_61, '#skF_3') | ~r1_tarski(A_61, '#skF_4'))), inference(resolution, [status(thm)], [c_161, c_109])).
% 2.67/1.37  tff(c_53, plain, (![A_4, A_37, B_38]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_37, B_38)))), inference(resolution, [status(thm)], [c_6, c_45])).
% 2.67/1.37  tff(c_182, plain, (![A_62]: (v1_relat_1(A_62) | ~r1_tarski(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_161, c_53])).
% 2.67/1.37  tff(c_194, plain, (![A_13]: (v1_relat_1(k7_relat_1('#skF_4', A_13)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_182])).
% 2.67/1.37  tff(c_199, plain, (![A_13]: (v1_relat_1(k7_relat_1('#skF_4', A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_194])).
% 2.67/1.37  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.67/1.37  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.67/1.37  tff(c_459, plain, (![C_135, A_136, B_137]: (m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))) | ~r1_tarski(k2_relat_1(C_135), B_137) | ~r1_tarski(k1_relat_1(C_135), A_136) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.37  tff(c_386, plain, (![A_116, B_117, C_118, D_119]: (k5_relset_1(A_116, B_117, C_118, D_119)=k7_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.67/1.37  tff(c_393, plain, (![D_119]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_119)=k7_relat_1('#skF_4', D_119))), inference(resolution, [status(thm)], [c_32, c_386])).
% 2.67/1.37  tff(c_30, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.67/1.37  tff(c_395, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_30])).
% 2.67/1.37  tff(c_462, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_459, c_395])).
% 2.67/1.37  tff(c_479, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_462])).
% 2.67/1.37  tff(c_506, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_479])).
% 2.67/1.37  tff(c_509, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_506])).
% 2.67/1.37  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_509])).
% 2.67/1.37  tff(c_514, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_479])).
% 2.67/1.37  tff(c_518, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_514])).
% 2.67/1.37  tff(c_521, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_518])).
% 2.67/1.37  tff(c_531, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_178, c_521])).
% 2.67/1.37  tff(c_534, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_531])).
% 2.67/1.37  tff(c_538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_534])).
% 2.67/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  Inference rules
% 2.67/1.37  ----------------------
% 2.67/1.37  #Ref     : 0
% 2.67/1.37  #Sup     : 105
% 2.67/1.37  #Fact    : 0
% 2.67/1.37  #Define  : 0
% 2.67/1.37  #Split   : 1
% 2.67/1.37  #Chain   : 0
% 2.67/1.37  #Close   : 0
% 2.67/1.37  
% 2.67/1.37  Ordering : KBO
% 2.67/1.37  
% 2.67/1.37  Simplification rules
% 2.67/1.37  ----------------------
% 2.67/1.37  #Subsume      : 7
% 2.67/1.37  #Demod        : 16
% 2.67/1.37  #Tautology    : 10
% 2.67/1.37  #SimpNegUnit  : 0
% 2.67/1.37  #BackRed      : 2
% 2.67/1.37  
% 2.67/1.37  #Partial instantiations: 0
% 2.67/1.37  #Strategies tried      : 1
% 2.67/1.37  
% 2.67/1.37  Timing (in seconds)
% 2.67/1.37  ----------------------
% 2.67/1.38  Preprocessing        : 0.30
% 2.67/1.38  Parsing              : 0.17
% 2.67/1.38  CNF conversion       : 0.02
% 2.67/1.38  Main loop            : 0.30
% 2.67/1.38  Inferencing          : 0.13
% 2.67/1.38  Reduction            : 0.07
% 2.67/1.38  Demodulation         : 0.05
% 2.67/1.38  BG Simplification    : 0.02
% 2.67/1.38  Subsumption          : 0.06
% 2.67/1.38  Abstraction          : 0.02
% 2.67/1.38  MUC search           : 0.00
% 2.67/1.38  Cooper               : 0.00
% 2.67/1.38  Total                : 0.64
% 2.67/1.38  Index Insertion      : 0.00
% 2.67/1.38  Index Deletion       : 0.00
% 2.67/1.38  Index Matching       : 0.00
% 2.67/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
