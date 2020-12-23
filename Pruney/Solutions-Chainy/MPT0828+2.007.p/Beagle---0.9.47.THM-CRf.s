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
% DateTime   : Thu Dec  3 10:07:18 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 165 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_50])).

tff(c_28,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_229,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(k2_relat_1(A_60),k2_relat_1(B_61))
      | ~ r1_tarski(A_60,B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_232,plain,(
    ! [A_7,B_61] :
      ( r1_tarski(A_7,k2_relat_1(B_61))
      | ~ r1_tarski(k6_relat_1(A_7),B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_229])).

tff(c_261,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,k2_relat_1(B_65))
      | ~ r1_tarski(k6_relat_1(A_64),B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_232])).

tff(c_264,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_261])).

tff(c_267,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_264])).

tff(c_356,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_360,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_356])).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_55,plain,(
    ! [C_28,A_29,B_30] :
      ( v4_relat_1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_59,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_55])).

tff(c_66,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = B_34
      | ~ v4_relat_1(B_34,A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_69,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_59,c_66])).

tff(c_72,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_69])).

tff(c_10,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_relat_1(A_43),k1_relat_1(B_44))
      | ~ r1_tarski(A_43,B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_116,plain,(
    ! [A_7,B_44] :
      ( r1_tarski(A_7,k1_relat_1(B_44))
      | ~ r1_tarski(k6_relat_1(A_7),B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_104])).

tff(c_125,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,k1_relat_1(B_46))
      | ~ r1_tarski(k6_relat_1(A_45),B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_116])).

tff(c_128,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_131,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_128])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( k1_relat_1(k7_relat_1(B_9,A_8)) = A_8
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_14])).

tff(c_137,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_72,c_134])).

tff(c_181,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_184,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_181])).

tff(c_186,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_184])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_186])).

tff(c_189,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_361,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_189])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.38  
% 2.24/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.38  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.38  
% 2.24/1.38  %Foreground sorts:
% 2.24/1.38  
% 2.24/1.38  
% 2.24/1.38  %Background operators:
% 2.24/1.38  
% 2.24/1.38  
% 2.24/1.38  %Foreground operators:
% 2.24/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.24/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.24/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.24/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.24/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.24/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.24/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.38  
% 2.44/1.40  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.44/1.40  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.44/1.40  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.44/1.40  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.44/1.40  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.44/1.40  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.44/1.40  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.44/1.40  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.44/1.40  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.44/1.40  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.44/1.40  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.40  tff(c_50, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.40  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_50])).
% 2.44/1.40  tff(c_28, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.40  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.44/1.40  tff(c_12, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.44/1.40  tff(c_229, plain, (![A_60, B_61]: (r1_tarski(k2_relat_1(A_60), k2_relat_1(B_61)) | ~r1_tarski(A_60, B_61) | ~v1_relat_1(B_61) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.40  tff(c_232, plain, (![A_7, B_61]: (r1_tarski(A_7, k2_relat_1(B_61)) | ~r1_tarski(k6_relat_1(A_7), B_61) | ~v1_relat_1(B_61) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_229])).
% 2.44/1.40  tff(c_261, plain, (![A_64, B_65]: (r1_tarski(A_64, k2_relat_1(B_65)) | ~r1_tarski(k6_relat_1(A_64), B_65) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_232])).
% 2.44/1.40  tff(c_264, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_261])).
% 2.44/1.40  tff(c_267, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_264])).
% 2.44/1.40  tff(c_356, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.44/1.40  tff(c_360, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_356])).
% 2.44/1.40  tff(c_26, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.44/1.40  tff(c_60, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.44/1.40  tff(c_55, plain, (![C_28, A_29, B_30]: (v4_relat_1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.44/1.40  tff(c_59, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_55])).
% 2.44/1.40  tff(c_66, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=B_34 | ~v4_relat_1(B_34, A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.44/1.40  tff(c_69, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_59, c_66])).
% 2.44/1.40  tff(c_72, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_69])).
% 2.44/1.40  tff(c_10, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.44/1.40  tff(c_104, plain, (![A_43, B_44]: (r1_tarski(k1_relat_1(A_43), k1_relat_1(B_44)) | ~r1_tarski(A_43, B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.44/1.40  tff(c_116, plain, (![A_7, B_44]: (r1_tarski(A_7, k1_relat_1(B_44)) | ~r1_tarski(k6_relat_1(A_7), B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_104])).
% 2.44/1.40  tff(c_125, plain, (![A_45, B_46]: (r1_tarski(A_45, k1_relat_1(B_46)) | ~r1_tarski(k6_relat_1(A_45), B_46) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_116])).
% 2.44/1.40  tff(c_128, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_125])).
% 2.44/1.40  tff(c_131, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_128])).
% 2.44/1.40  tff(c_14, plain, (![B_9, A_8]: (k1_relat_1(k7_relat_1(B_9, A_8))=A_8 | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.40  tff(c_134, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_131, c_14])).
% 2.44/1.40  tff(c_137, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_72, c_134])).
% 2.44/1.40  tff(c_181, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.44/1.40  tff(c_184, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_181])).
% 2.44/1.40  tff(c_186, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_184])).
% 2.44/1.40  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_186])).
% 2.44/1.40  tff(c_189, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 2.44/1.40  tff(c_361, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_189])).
% 2.44/1.40  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_361])).
% 2.44/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.40  
% 2.44/1.40  Inference rules
% 2.44/1.40  ----------------------
% 2.44/1.40  #Ref     : 0
% 2.44/1.40  #Sup     : 76
% 2.44/1.40  #Fact    : 0
% 2.44/1.40  #Define  : 0
% 2.44/1.40  #Split   : 1
% 2.44/1.40  #Chain   : 0
% 2.44/1.40  #Close   : 0
% 2.44/1.40  
% 2.44/1.40  Ordering : KBO
% 2.44/1.40  
% 2.44/1.40  Simplification rules
% 2.44/1.40  ----------------------
% 2.44/1.40  #Subsume      : 0
% 2.44/1.40  #Demod        : 32
% 2.44/1.40  #Tautology    : 27
% 2.44/1.40  #SimpNegUnit  : 1
% 2.44/1.40  #BackRed      : 2
% 2.44/1.40  
% 2.44/1.40  #Partial instantiations: 0
% 2.44/1.40  #Strategies tried      : 1
% 2.44/1.40  
% 2.44/1.40  Timing (in seconds)
% 2.44/1.40  ----------------------
% 2.44/1.40  Preprocessing        : 0.31
% 2.44/1.40  Parsing              : 0.17
% 2.44/1.40  CNF conversion       : 0.02
% 2.44/1.40  Main loop            : 0.23
% 2.44/1.40  Inferencing          : 0.09
% 2.44/1.40  Reduction            : 0.07
% 2.44/1.40  Demodulation         : 0.05
% 2.44/1.40  BG Simplification    : 0.01
% 2.44/1.40  Subsumption          : 0.03
% 2.44/1.40  Abstraction          : 0.01
% 2.44/1.40  MUC search           : 0.00
% 2.44/1.40  Cooper               : 0.00
% 2.44/1.40  Total                : 0.57
% 2.44/1.40  Index Insertion      : 0.00
% 2.44/1.40  Index Deletion       : 0.00
% 2.44/1.40  Index Matching       : 0.00
% 2.44/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
