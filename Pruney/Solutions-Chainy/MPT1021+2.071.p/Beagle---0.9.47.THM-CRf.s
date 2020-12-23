%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:11 EST 2020

% Result     : Theorem 6.12s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 359 expanded)
%              Number of leaves         :   44 ( 155 expanded)
%              Depth                    :    9
%              Number of atoms          :  276 (1083 expanded)
%              Number of equality atoms :   40 (  82 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_149,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2416,plain,(
    ! [B_199,A_200] :
      ( v1_relat_1(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_200))
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2422,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_2416])).

tff(c_2431,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2422])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_56,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2642,plain,(
    ! [C_243,A_244,B_245] :
      ( v2_funct_1(C_243)
      | ~ v3_funct_2(C_243,A_244,B_245)
      | ~ v1_funct_1(C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2648,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2642])).

tff(c_2656,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2648])).

tff(c_42,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2704,plain,(
    ! [A_254,B_255,C_256,D_257] :
      ( r2_relset_1(A_254,B_255,C_256,C_256)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255)))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2714,plain,(
    ! [A_258,C_259] :
      ( r2_relset_1(A_258,A_258,C_259,C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_258,A_258))) ) ),
    inference(resolution,[status(thm)],[c_42,c_2704])).

tff(c_2722,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_42,c_2714])).

tff(c_2433,plain,(
    ! [C_201,B_202,A_203] :
      ( v5_relat_1(C_201,B_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2445,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_2433])).

tff(c_2468,plain,(
    ! [B_216,A_217] :
      ( k2_relat_1(B_216) = A_217
      | ~ v2_funct_2(B_216,A_217)
      | ~ v5_relat_1(B_216,A_217)
      | ~ v1_relat_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2477,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2445,c_2468])).

tff(c_2484,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_2477])).

tff(c_2485,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2484])).

tff(c_2558,plain,(
    ! [C_231,B_232,A_233] :
      ( v2_funct_2(C_231,B_232)
      | ~ v3_funct_2(C_231,A_233,B_232)
      | ~ v1_funct_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_233,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2564,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2558])).

tff(c_2572,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_2564])).

tff(c_2574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2485,c_2572])).

tff(c_2575,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2484])).

tff(c_48,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_relat_1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ! [A_8] :
      ( k5_relat_1(k2_funct_1(A_8),A_8) = k6_partfun1(k2_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2742,plain,(
    ! [A_263,B_264] :
      ( k2_funct_2(A_263,B_264) = k2_funct_1(B_264)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(k2_zfmisc_1(A_263,A_263)))
      | ~ v3_funct_2(B_264,A_263,A_263)
      | ~ v1_funct_2(B_264,A_263,A_263)
      | ~ v1_funct_1(B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2748,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2742])).

tff(c_2756,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_2748])).

tff(c_2725,plain,(
    ! [A_260,B_261] :
      ( v1_funct_1(k2_funct_2(A_260,B_261))
      | ~ m1_subset_1(B_261,k1_zfmisc_1(k2_zfmisc_1(A_260,A_260)))
      | ~ v3_funct_2(B_261,A_260,A_260)
      | ~ v1_funct_2(B_261,A_260,A_260)
      | ~ v1_funct_1(B_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2731,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2725])).

tff(c_2739,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_2731])).

tff(c_2758,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2756,c_2739])).

tff(c_32,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_funct_2(A_24,B_25),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v3_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2935,plain,(
    ! [A_289,C_285,E_287,F_284,B_288,D_286] :
      ( k1_partfun1(A_289,B_288,C_285,D_286,E_287,F_284) = k5_relat_1(E_287,F_284)
      | ~ m1_subset_1(F_284,k1_zfmisc_1(k2_zfmisc_1(C_285,D_286)))
      | ~ v1_funct_1(F_284)
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_289,B_288)))
      | ~ v1_funct_1(E_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2943,plain,(
    ! [A_289,B_288,E_287] :
      ( k1_partfun1(A_289,B_288,'#skF_2','#skF_2',E_287,'#skF_3') = k5_relat_1(E_287,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_287,k1_zfmisc_1(k2_zfmisc_1(A_289,B_288)))
      | ~ v1_funct_1(E_287) ) ),
    inference(resolution,[status(thm)],[c_54,c_2935])).

tff(c_2967,plain,(
    ! [A_290,B_291,E_292] :
      ( k1_partfun1(A_290,B_291,'#skF_2','#skF_2',E_292,'#skF_3') = k5_relat_1(E_292,'#skF_3')
      | ~ m1_subset_1(E_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291)))
      | ~ v1_funct_1(E_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2943])).

tff(c_3243,plain,(
    ! [A_301,B_302] :
      ( k1_partfun1(A_301,A_301,'#skF_2','#skF_2',k2_funct_2(A_301,B_302),'#skF_3') = k5_relat_1(k2_funct_2(A_301,B_302),'#skF_3')
      | ~ v1_funct_1(k2_funct_2(A_301,B_302))
      | ~ m1_subset_1(B_302,k1_zfmisc_1(k2_zfmisc_1(A_301,A_301)))
      | ~ v3_funct_2(B_302,A_301,A_301)
      | ~ v1_funct_2(B_302,A_301,A_301)
      | ~ v1_funct_1(B_302) ) ),
    inference(resolution,[status(thm)],[c_32,c_2967])).

tff(c_3255,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3') = k5_relat_1(k2_funct_2('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_3243])).

tff(c_3272,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_2758,c_2756,c_2756,c_2756,c_3255])).

tff(c_78,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_78])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_304,plain,(
    ! [C_89,A_90,B_91] :
      ( v2_funct_1(C_89)
      | ~ v3_funct_2(C_89,A_90,B_91)
      | ~ v1_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_310,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_304])).

tff(c_318,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_310])).

tff(c_356,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( r2_relset_1(A_99,B_100,C_101,C_101)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_387,plain,(
    ! [A_104,C_105] :
      ( r2_relset_1(A_104,A_104,C_105,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,A_104))) ) ),
    inference(resolution,[status(thm)],[c_42,c_356])).

tff(c_395,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_42,c_387])).

tff(c_250,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_262,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_250])).

tff(c_338,plain,(
    ! [A_97,B_98] :
      ( k1_relset_1(A_97,A_97,B_98) = A_97
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k2_zfmisc_1(A_97,A_97)))
      | ~ v1_funct_2(B_98,A_97,A_97)
      | ~ v1_funct_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_344,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_338])).

tff(c_353,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_262,c_344])).

tff(c_12,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_relat_1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k2_funct_1(A_8)) = k6_partfun1(k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_434,plain,(
    ! [A_115,B_116] :
      ( k2_funct_2(A_115,B_116) = k2_funct_1(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_zfmisc_1(A_115,A_115)))
      | ~ v3_funct_2(B_116,A_115,A_115)
      | ~ v1_funct_2(B_116,A_115,A_115)
      | ~ v1_funct_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_440,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_434])).

tff(c_448,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_440])).

tff(c_415,plain,(
    ! [A_111,B_112] :
      ( v1_funct_1(k2_funct_2(A_111,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k2_zfmisc_1(A_111,A_111)))
      | ~ v3_funct_2(B_112,A_111,A_111)
      | ~ v1_funct_2(B_112,A_111,A_111)
      | ~ v1_funct_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_421,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_415])).

tff(c_429,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_421])).

tff(c_450,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_429])).

tff(c_624,plain,(
    ! [F_134,A_139,E_137,D_136,B_138,C_135] :
      ( k1_partfun1(A_139,B_138,C_135,D_136,E_137,F_134) = k5_relat_1(E_137,F_134)
      | ~ m1_subset_1(F_134,k1_zfmisc_1(k2_zfmisc_1(C_135,D_136)))
      | ~ v1_funct_1(F_134)
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_1(E_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2270,plain,(
    ! [B_191,A_194,E_193,A_192,B_195] :
      ( k1_partfun1(A_192,B_195,A_194,A_194,E_193,k2_funct_2(A_194,B_191)) = k5_relat_1(E_193,k2_funct_2(A_194,B_191))
      | ~ v1_funct_1(k2_funct_2(A_194,B_191))
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_195)))
      | ~ v1_funct_1(E_193)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_191,A_194,A_194)
      | ~ v1_funct_2(B_191,A_194,A_194)
      | ~ v1_funct_1(B_191) ) ),
    inference(resolution,[status(thm)],[c_32,c_624])).

tff(c_2292,plain,(
    ! [A_194,B_191] :
      ( k1_partfun1('#skF_2','#skF_2',A_194,A_194,'#skF_3',k2_funct_2(A_194,B_191)) = k5_relat_1('#skF_3',k2_funct_2(A_194,B_191))
      | ~ v1_funct_1(k2_funct_2(A_194,B_191))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1(A_194,A_194)))
      | ~ v3_funct_2(B_191,A_194,A_194)
      | ~ v1_funct_2(B_191,A_194,A_194)
      | ~ v1_funct_1(B_191) ) ),
    inference(resolution,[status(thm)],[c_54,c_2270])).

tff(c_2346,plain,(
    ! [A_196,B_197] :
      ( k1_partfun1('#skF_2','#skF_2',A_196,A_196,'#skF_3',k2_funct_2(A_196,B_197)) = k5_relat_1('#skF_3',k2_funct_2(A_196,B_197))
      | ~ v1_funct_1(k2_funct_2(A_196,B_197))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(k2_zfmisc_1(A_196,A_196)))
      | ~ v3_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_2(B_197,A_196,A_196)
      | ~ v1_funct_1(B_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2292])).

tff(c_2368,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k5_relat_1('#skF_3',k2_funct_2('#skF_2','#skF_3'))
    | ~ v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2346])).

tff(c_2400,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_450,c_448,c_448,c_448,c_2368])).

tff(c_52,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_76,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_451,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_76])).

tff(c_2402,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2400,c_451])).

tff(c_2409,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2402])).

tff(c_2412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_60,c_318,c_395,c_353,c_2409])).

tff(c_2413,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2759,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2756,c_2413])).

tff(c_3387,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_2759])).

tff(c_3444,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1(k2_relat_1('#skF_3')),k6_partfun1('#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_3387])).

tff(c_3447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2431,c_60,c_2656,c_2722,c_2575,c_3444])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.12/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.23  
% 6.12/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.24  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_subset_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3
% 6.12/2.24  
% 6.12/2.24  %Foreground sorts:
% 6.12/2.24  
% 6.12/2.24  
% 6.12/2.24  %Background operators:
% 6.12/2.24  
% 6.12/2.24  
% 6.12/2.24  %Foreground operators:
% 6.12/2.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.12/2.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.12/2.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.12/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.12/2.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.12/2.24  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.12/2.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.12/2.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.12/2.24  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.12/2.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.12/2.24  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.12/2.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.12/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.12/2.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.12/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.12/2.24  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.12/2.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.12/2.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.12/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.12/2.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.12/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.12/2.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.12/2.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.12/2.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.12/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.12/2.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.12/2.24  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.12/2.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.12/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.12/2.24  
% 6.39/2.26  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.39/2.26  tff(f_149, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 6.39/2.26  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.39/2.26  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.39/2.26  tff(f_106, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.39/2.26  tff(f_66, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 6.39/2.26  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.39/2.26  tff(f_86, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.39/2.26  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.39/2.26  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.39/2.26  tff(f_126, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.39/2.26  tff(f_102, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.39/2.26  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.39/2.26  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.39/2.26  tff(f_136, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 6.39/2.26  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.39/2.26  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.39/2.26  tff(c_2416, plain, (![B_199, A_200]: (v1_relat_1(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(A_200)) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.39/2.26  tff(c_2422, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_2416])).
% 6.39/2.26  tff(c_2431, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2422])).
% 6.39/2.26  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.39/2.26  tff(c_56, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.39/2.26  tff(c_2642, plain, (![C_243, A_244, B_245]: (v2_funct_1(C_243) | ~v3_funct_2(C_243, A_244, B_245) | ~v1_funct_1(C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.39/2.26  tff(c_2648, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2642])).
% 6.39/2.26  tff(c_2656, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2648])).
% 6.39/2.26  tff(c_42, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.39/2.26  tff(c_2704, plain, (![A_254, B_255, C_256, D_257]: (r2_relset_1(A_254, B_255, C_256, C_256) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.39/2.26  tff(c_2714, plain, (![A_258, C_259]: (r2_relset_1(A_258, A_258, C_259, C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_258, A_258))))), inference(resolution, [status(thm)], [c_42, c_2704])).
% 6.39/2.26  tff(c_2722, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_42, c_2714])).
% 6.39/2.26  tff(c_2433, plain, (![C_201, B_202, A_203]: (v5_relat_1(C_201, B_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.39/2.26  tff(c_2445, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_2433])).
% 6.39/2.26  tff(c_2468, plain, (![B_216, A_217]: (k2_relat_1(B_216)=A_217 | ~v2_funct_2(B_216, A_217) | ~v5_relat_1(B_216, A_217) | ~v1_relat_1(B_216))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.39/2.26  tff(c_2477, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2445, c_2468])).
% 6.39/2.26  tff(c_2484, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2431, c_2477])).
% 6.39/2.26  tff(c_2485, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2484])).
% 6.39/2.26  tff(c_2558, plain, (![C_231, B_232, A_233]: (v2_funct_2(C_231, B_232) | ~v3_funct_2(C_231, A_233, B_232) | ~v1_funct_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_233, B_232))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.39/2.26  tff(c_2564, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2558])).
% 6.39/2.26  tff(c_2572, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_2564])).
% 6.39/2.26  tff(c_2574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2485, c_2572])).
% 6.39/2.26  tff(c_2575, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_2484])).
% 6.39/2.26  tff(c_48, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.39/2.26  tff(c_10, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_relat_1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.39/2.26  tff(c_62, plain, (![A_8]: (k5_relat_1(k2_funct_1(A_8), A_8)=k6_partfun1(k2_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 6.39/2.26  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.39/2.26  tff(c_2742, plain, (![A_263, B_264]: (k2_funct_2(A_263, B_264)=k2_funct_1(B_264) | ~m1_subset_1(B_264, k1_zfmisc_1(k2_zfmisc_1(A_263, A_263))) | ~v3_funct_2(B_264, A_263, A_263) | ~v1_funct_2(B_264, A_263, A_263) | ~v1_funct_1(B_264))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.39/2.26  tff(c_2748, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2742])).
% 6.39/2.26  tff(c_2756, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_2748])).
% 6.39/2.26  tff(c_2725, plain, (![A_260, B_261]: (v1_funct_1(k2_funct_2(A_260, B_261)) | ~m1_subset_1(B_261, k1_zfmisc_1(k2_zfmisc_1(A_260, A_260))) | ~v3_funct_2(B_261, A_260, A_260) | ~v1_funct_2(B_261, A_260, A_260) | ~v1_funct_1(B_261))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.39/2.26  tff(c_2731, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2725])).
% 6.39/2.26  tff(c_2739, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_2731])).
% 6.39/2.26  tff(c_2758, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2756, c_2739])).
% 6.39/2.26  tff(c_32, plain, (![A_24, B_25]: (m1_subset_1(k2_funct_2(A_24, B_25), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v3_funct_2(B_25, A_24, A_24) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.39/2.26  tff(c_2935, plain, (![A_289, C_285, E_287, F_284, B_288, D_286]: (k1_partfun1(A_289, B_288, C_285, D_286, E_287, F_284)=k5_relat_1(E_287, F_284) | ~m1_subset_1(F_284, k1_zfmisc_1(k2_zfmisc_1(C_285, D_286))) | ~v1_funct_1(F_284) | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_289, B_288))) | ~v1_funct_1(E_287))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.39/2.26  tff(c_2943, plain, (![A_289, B_288, E_287]: (k1_partfun1(A_289, B_288, '#skF_2', '#skF_2', E_287, '#skF_3')=k5_relat_1(E_287, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_287, k1_zfmisc_1(k2_zfmisc_1(A_289, B_288))) | ~v1_funct_1(E_287))), inference(resolution, [status(thm)], [c_54, c_2935])).
% 6.39/2.26  tff(c_2967, plain, (![A_290, B_291, E_292]: (k1_partfun1(A_290, B_291, '#skF_2', '#skF_2', E_292, '#skF_3')=k5_relat_1(E_292, '#skF_3') | ~m1_subset_1(E_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))) | ~v1_funct_1(E_292))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2943])).
% 6.39/2.26  tff(c_3243, plain, (![A_301, B_302]: (k1_partfun1(A_301, A_301, '#skF_2', '#skF_2', k2_funct_2(A_301, B_302), '#skF_3')=k5_relat_1(k2_funct_2(A_301, B_302), '#skF_3') | ~v1_funct_1(k2_funct_2(A_301, B_302)) | ~m1_subset_1(B_302, k1_zfmisc_1(k2_zfmisc_1(A_301, A_301))) | ~v3_funct_2(B_302, A_301, A_301) | ~v1_funct_2(B_302, A_301, A_301) | ~v1_funct_1(B_302))), inference(resolution, [status(thm)], [c_32, c_2967])).
% 6.39/2.26  tff(c_3255, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3')=k5_relat_1(k2_funct_2('#skF_2', '#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_3243])).
% 6.39/2.26  tff(c_3272, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_2758, c_2756, c_2756, c_2756, c_3255])).
% 6.39/2.26  tff(c_78, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.39/2.26  tff(c_84, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_78])).
% 6.39/2.26  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_84])).
% 6.39/2.26  tff(c_304, plain, (![C_89, A_90, B_91]: (v2_funct_1(C_89) | ~v3_funct_2(C_89, A_90, B_91) | ~v1_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.39/2.26  tff(c_310, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_304])).
% 6.39/2.26  tff(c_318, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_310])).
% 6.39/2.26  tff(c_356, plain, (![A_99, B_100, C_101, D_102]: (r2_relset_1(A_99, B_100, C_101, C_101) | ~m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.39/2.26  tff(c_387, plain, (![A_104, C_105]: (r2_relset_1(A_104, A_104, C_105, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, A_104))))), inference(resolution, [status(thm)], [c_42, c_356])).
% 6.39/2.26  tff(c_395, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_42, c_387])).
% 6.39/2.26  tff(c_250, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.39/2.26  tff(c_262, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_250])).
% 6.39/2.26  tff(c_338, plain, (![A_97, B_98]: (k1_relset_1(A_97, A_97, B_98)=A_97 | ~m1_subset_1(B_98, k1_zfmisc_1(k2_zfmisc_1(A_97, A_97))) | ~v1_funct_2(B_98, A_97, A_97) | ~v1_funct_1(B_98))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.39/2.26  tff(c_344, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_338])).
% 6.39/2.26  tff(c_353, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_262, c_344])).
% 6.39/2.26  tff(c_12, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_relat_1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.39/2.26  tff(c_61, plain, (![A_8]: (k5_relat_1(A_8, k2_funct_1(A_8))=k6_partfun1(k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 6.39/2.26  tff(c_434, plain, (![A_115, B_116]: (k2_funct_2(A_115, B_116)=k2_funct_1(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(k2_zfmisc_1(A_115, A_115))) | ~v3_funct_2(B_116, A_115, A_115) | ~v1_funct_2(B_116, A_115, A_115) | ~v1_funct_1(B_116))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.39/2.26  tff(c_440, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_434])).
% 6.39/2.26  tff(c_448, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_440])).
% 6.39/2.26  tff(c_415, plain, (![A_111, B_112]: (v1_funct_1(k2_funct_2(A_111, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(k2_zfmisc_1(A_111, A_111))) | ~v3_funct_2(B_112, A_111, A_111) | ~v1_funct_2(B_112, A_111, A_111) | ~v1_funct_1(B_112))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.39/2.26  tff(c_421, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_415])).
% 6.39/2.26  tff(c_429, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_421])).
% 6.39/2.26  tff(c_450, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_429])).
% 6.39/2.26  tff(c_624, plain, (![F_134, A_139, E_137, D_136, B_138, C_135]: (k1_partfun1(A_139, B_138, C_135, D_136, E_137, F_134)=k5_relat_1(E_137, F_134) | ~m1_subset_1(F_134, k1_zfmisc_1(k2_zfmisc_1(C_135, D_136))) | ~v1_funct_1(F_134) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_1(E_137))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.39/2.26  tff(c_2270, plain, (![B_191, A_194, E_193, A_192, B_195]: (k1_partfun1(A_192, B_195, A_194, A_194, E_193, k2_funct_2(A_194, B_191))=k5_relat_1(E_193, k2_funct_2(A_194, B_191)) | ~v1_funct_1(k2_funct_2(A_194, B_191)) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_195))) | ~v1_funct_1(E_193) | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_191, A_194, A_194) | ~v1_funct_2(B_191, A_194, A_194) | ~v1_funct_1(B_191))), inference(resolution, [status(thm)], [c_32, c_624])).
% 6.39/2.26  tff(c_2292, plain, (![A_194, B_191]: (k1_partfun1('#skF_2', '#skF_2', A_194, A_194, '#skF_3', k2_funct_2(A_194, B_191))=k5_relat_1('#skF_3', k2_funct_2(A_194, B_191)) | ~v1_funct_1(k2_funct_2(A_194, B_191)) | ~v1_funct_1('#skF_3') | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1(A_194, A_194))) | ~v3_funct_2(B_191, A_194, A_194) | ~v1_funct_2(B_191, A_194, A_194) | ~v1_funct_1(B_191))), inference(resolution, [status(thm)], [c_54, c_2270])).
% 6.39/2.26  tff(c_2346, plain, (![A_196, B_197]: (k1_partfun1('#skF_2', '#skF_2', A_196, A_196, '#skF_3', k2_funct_2(A_196, B_197))=k5_relat_1('#skF_3', k2_funct_2(A_196, B_197)) | ~v1_funct_1(k2_funct_2(A_196, B_197)) | ~m1_subset_1(B_197, k1_zfmisc_1(k2_zfmisc_1(A_196, A_196))) | ~v3_funct_2(B_197, A_196, A_196) | ~v1_funct_2(B_197, A_196, A_196) | ~v1_funct_1(B_197))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2292])).
% 6.39/2.26  tff(c_2368, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k5_relat_1('#skF_3', k2_funct_2('#skF_2', '#skF_3')) | ~v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2346])).
% 6.39/2.26  tff(c_2400, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_450, c_448, c_448, c_448, c_2368])).
% 6.39/2.26  tff(c_52, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.39/2.26  tff(c_76, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_52])).
% 6.39/2.26  tff(c_451, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_448, c_76])).
% 6.39/2.26  tff(c_2402, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2400, c_451])).
% 6.39/2.26  tff(c_2409, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_61, c_2402])).
% 6.39/2.26  tff(c_2412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_60, c_318, c_395, c_353, c_2409])).
% 6.39/2.26  tff(c_2413, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_52])).
% 6.39/2.26  tff(c_2759, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2756, c_2413])).
% 6.39/2.26  tff(c_3387, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_2759])).
% 6.39/2.26  tff(c_3444, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1(k2_relat_1('#skF_3')), k6_partfun1('#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_62, c_3387])).
% 6.39/2.26  tff(c_3447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2431, c_60, c_2656, c_2722, c_2575, c_3444])).
% 6.39/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.26  
% 6.39/2.26  Inference rules
% 6.39/2.26  ----------------------
% 6.39/2.26  #Ref     : 0
% 6.39/2.26  #Sup     : 724
% 6.39/2.26  #Fact    : 0
% 6.39/2.26  #Define  : 0
% 6.39/2.26  #Split   : 3
% 6.39/2.26  #Chain   : 0
% 6.39/2.26  #Close   : 0
% 6.39/2.26  
% 6.39/2.26  Ordering : KBO
% 6.39/2.26  
% 6.39/2.26  Simplification rules
% 6.39/2.26  ----------------------
% 6.39/2.26  #Subsume      : 6
% 6.39/2.26  #Demod        : 1657
% 6.39/2.26  #Tautology    : 286
% 6.39/2.26  #SimpNegUnit  : 2
% 6.39/2.26  #BackRed      : 60
% 6.39/2.26  
% 6.39/2.26  #Partial instantiations: 0
% 6.39/2.26  #Strategies tried      : 1
% 6.39/2.26  
% 6.39/2.26  Timing (in seconds)
% 6.39/2.26  ----------------------
% 6.39/2.26  Preprocessing        : 0.36
% 6.39/2.26  Parsing              : 0.19
% 6.39/2.26  CNF conversion       : 0.02
% 6.39/2.26  Main loop            : 1.12
% 6.39/2.26  Inferencing          : 0.38
% 6.39/2.26  Reduction            : 0.43
% 6.39/2.26  Demodulation         : 0.33
% 6.39/2.26  BG Simplification    : 0.04
% 6.39/2.26  Subsumption          : 0.19
% 6.39/2.26  Abstraction          : 0.05
% 6.39/2.26  MUC search           : 0.00
% 6.39/2.27  Cooper               : 0.00
% 6.39/2.27  Total                : 1.53
% 6.39/2.27  Index Insertion      : 0.00
% 6.39/2.27  Index Deletion       : 0.00
% 6.39/2.27  Index Matching       : 0.00
% 6.39/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
