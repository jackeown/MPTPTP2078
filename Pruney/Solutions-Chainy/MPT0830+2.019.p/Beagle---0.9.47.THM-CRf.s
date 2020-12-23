%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:28 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_43,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k7_relat_1(B_11,A_10),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_33,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_151,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,k2_zfmisc_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41,c_151])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,(
    ! [A_4,B_54,A_55] :
      ( v5_relat_1(A_4,B_54)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_55,B_54)) ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_184,plain,(
    ! [A_62] :
      ( v5_relat_1(A_62,'#skF_3')
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_167,c_128])).

tff(c_51,plain,(
    ! [A_4,A_36,B_37] :
      ( v1_relat_1(A_4)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_36,B_37)) ) ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_188,plain,(
    ! [A_63] :
      ( v1_relat_1(A_63)
      | ~ r1_tarski(A_63,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_167,c_51])).

tff(c_200,plain,(
    ! [A_10] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_10))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_188])).

tff(c_205,plain,(
    ! [A_10] : v1_relat_1(k7_relat_1('#skF_4',A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_200])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_251,plain,(
    ! [C_80,A_81,B_82] :
      ( m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ r1_tarski(k2_relat_1(C_80),B_82)
      | ~ r1_tarski(k1_relat_1(C_80),A_81)
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_208,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k5_relset_1(A_66,B_67,C_68,D_69) = k7_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_215,plain,(
    ! [D_69] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_69) = k7_relat_1('#skF_4',D_69) ),
    inference(resolution,[status(thm)],[c_30,c_208])).

tff(c_28,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_219,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_28])).

tff(c_254,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_251,c_219])).

tff(c_271,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_254])).

tff(c_383,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_386,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_383])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_386])).

tff(c_391,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_395,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_391])).

tff(c_398,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_395])).

tff(c_402,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_184,c_398])).

tff(c_405,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_402])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.30  
% 2.45/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.31  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.45/1.31  
% 2.45/1.31  %Foreground sorts:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Background operators:
% 2.45/1.31  
% 2.45/1.31  
% 2.45/1.31  %Foreground operators:
% 2.45/1.31  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.45/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.45/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.31  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.45/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.31  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.45/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.31  
% 2.45/1.32  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.45/1.32  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.45/1.32  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.45/1.32  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.45/1.32  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.45/1.32  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.45/1.32  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.45/1.32  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.45/1.32  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.45/1.32  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.45/1.32  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.32  tff(c_43, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.45/1.32  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_43])).
% 2.45/1.32  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k7_relat_1(B_11, A_10), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.45/1.32  tff(c_33, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.32  tff(c_41, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_33])).
% 2.45/1.32  tff(c_151, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.32  tff(c_167, plain, (![A_62]: (r1_tarski(A_62, k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_41, c_151])).
% 2.45/1.32  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.45/1.32  tff(c_120, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.32  tff(c_128, plain, (![A_4, B_54, A_55]: (v5_relat_1(A_4, B_54) | ~r1_tarski(A_4, k2_zfmisc_1(A_55, B_54)))), inference(resolution, [status(thm)], [c_6, c_120])).
% 2.45/1.32  tff(c_184, plain, (![A_62]: (v5_relat_1(A_62, '#skF_3') | ~r1_tarski(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_167, c_128])).
% 2.45/1.32  tff(c_51, plain, (![A_4, A_36, B_37]: (v1_relat_1(A_4) | ~r1_tarski(A_4, k2_zfmisc_1(A_36, B_37)))), inference(resolution, [status(thm)], [c_6, c_43])).
% 2.45/1.32  tff(c_188, plain, (![A_63]: (v1_relat_1(A_63) | ~r1_tarski(A_63, '#skF_4'))), inference(resolution, [status(thm)], [c_167, c_51])).
% 2.45/1.32  tff(c_200, plain, (![A_10]: (v1_relat_1(k7_relat_1('#skF_4', A_10)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_188])).
% 2.45/1.32  tff(c_205, plain, (![A_10]: (v1_relat_1(k7_relat_1('#skF_4', A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_200])).
% 2.45/1.32  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.45/1.32  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.32  tff(c_251, plain, (![C_80, A_81, B_82]: (m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~r1_tarski(k2_relat_1(C_80), B_82) | ~r1_tarski(k1_relat_1(C_80), A_81) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.45/1.32  tff(c_208, plain, (![A_66, B_67, C_68, D_69]: (k5_relset_1(A_66, B_67, C_68, D_69)=k7_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.45/1.32  tff(c_215, plain, (![D_69]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_69)=k7_relat_1('#skF_4', D_69))), inference(resolution, [status(thm)], [c_30, c_208])).
% 2.45/1.32  tff(c_28, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.45/1.32  tff(c_219, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_28])).
% 2.45/1.32  tff(c_254, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_251, c_219])).
% 2.45/1.32  tff(c_271, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_254])).
% 2.45/1.32  tff(c_383, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_271])).
% 2.45/1.32  tff(c_386, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_383])).
% 2.45/1.32  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_386])).
% 2.45/1.32  tff(c_391, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_271])).
% 2.45/1.32  tff(c_395, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_391])).
% 2.45/1.32  tff(c_398, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_395])).
% 2.45/1.32  tff(c_402, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_184, c_398])).
% 2.45/1.32  tff(c_405, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_402])).
% 2.45/1.32  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_405])).
% 2.45/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.32  
% 2.45/1.32  Inference rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Ref     : 0
% 2.45/1.32  #Sup     : 76
% 2.45/1.32  #Fact    : 0
% 2.45/1.32  #Define  : 0
% 2.45/1.32  #Split   : 1
% 2.45/1.32  #Chain   : 0
% 2.45/1.32  #Close   : 0
% 2.45/1.32  
% 2.45/1.32  Ordering : KBO
% 2.45/1.32  
% 2.45/1.32  Simplification rules
% 2.45/1.32  ----------------------
% 2.45/1.32  #Subsume      : 6
% 2.45/1.32  #Demod        : 11
% 2.45/1.32  #Tautology    : 9
% 2.45/1.32  #SimpNegUnit  : 0
% 2.45/1.32  #BackRed      : 2
% 2.45/1.32  
% 2.45/1.32  #Partial instantiations: 0
% 2.45/1.32  #Strategies tried      : 1
% 2.45/1.32  
% 2.45/1.32  Timing (in seconds)
% 2.45/1.32  ----------------------
% 2.45/1.32  Preprocessing        : 0.30
% 2.45/1.32  Parsing              : 0.16
% 2.45/1.32  CNF conversion       : 0.02
% 2.45/1.32  Main loop            : 0.26
% 2.45/1.32  Inferencing          : 0.11
% 2.45/1.32  Reduction            : 0.06
% 2.45/1.32  Demodulation         : 0.04
% 2.45/1.32  BG Simplification    : 0.01
% 2.45/1.32  Subsumption          : 0.05
% 2.45/1.32  Abstraction          : 0.01
% 2.45/1.32  MUC search           : 0.00
% 2.45/1.32  Cooper               : 0.00
% 2.45/1.32  Total                : 0.59
% 2.45/1.32  Index Insertion      : 0.00
% 2.45/1.32  Index Deletion       : 0.00
% 2.45/1.32  Index Matching       : 0.00
% 2.45/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
