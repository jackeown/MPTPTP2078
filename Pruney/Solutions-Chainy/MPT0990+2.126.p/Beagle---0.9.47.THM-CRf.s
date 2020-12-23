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
% DateTime   : Thu Dec  3 10:13:14 EST 2020

% Result     : Theorem 9.02s
% Output     : CNFRefutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :  163 (1298 expanded)
%              Number of leaves         :   56 ( 485 expanded)
%              Depth                    :   21
%              Number of atoms          :  345 (4613 expanded)
%              Number of equality atoms :   94 (1317 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_255,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_164,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_202,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_168,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_190,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_178,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_176,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_200,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_150,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_219,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_140,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_158,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_86,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_14,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_98,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_198,plain,(
    ! [B_91,A_92] :
      ( v1_relat_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_210,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_98,c_198])).

tff(c_220,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_210])).

tff(c_102,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_285,plain,(
    ! [C_103,A_104,B_105] :
      ( v4_relat_1(C_103,A_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_302,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_285])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_207,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_104,c_198])).

tff(c_217,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_207])).

tff(c_108,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_76,plain,(
    ! [A_64] : k6_relat_1(A_64) = k6_partfun1(A_64) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_40,plain,(
    ! [A_32] : v2_funct_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_112,plain,(
    ! [A_32] : v2_funct_1(k6_partfun1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40])).

tff(c_96,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_1110,plain,(
    ! [A_180,B_181,C_182] :
      ( k2_relset_1(A_180,B_181,C_182) = k2_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1123,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_1110])).

tff(c_1132,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1123])).

tff(c_70,plain,(
    ! [D_55,F_57,B_53,A_52,E_56,C_54] :
      ( m1_subset_1(k1_partfun1(A_52,B_53,C_54,D_55,E_56,F_57),k1_zfmisc_1(k2_zfmisc_1(A_52,D_55)))
      | ~ m1_subset_1(F_57,k1_zfmisc_1(k2_zfmisc_1(C_54,D_55)))
      | ~ v1_funct_1(F_57)
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ v1_funct_1(E_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_68,plain,(
    ! [A_51] : m1_subset_1(k6_relat_1(A_51),k1_zfmisc_1(k2_zfmisc_1(A_51,A_51))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_109,plain,(
    ! [A_51] : m1_subset_1(k6_partfun1(A_51),k1_zfmisc_1(k2_zfmisc_1(A_51,A_51))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_68])).

tff(c_94,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_2613,plain,(
    ! [D_225,C_226,A_227,B_228] :
      ( D_225 = C_226
      | ~ r2_relset_1(A_227,B_228,C_226,D_225)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_2627,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_94,c_2613])).

tff(c_2650,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2627])).

tff(c_2840,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2650])).

tff(c_3154,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2840])).

tff(c_3161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_104,c_102,c_98,c_3154])).

tff(c_3162,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2650])).

tff(c_3360,plain,(
    ! [D_268,A_269,B_267,E_271,F_270,C_272] :
      ( k1_partfun1(A_269,B_267,C_272,D_268,E_271,F_270) = k5_relat_1(E_271,F_270)
      | ~ m1_subset_1(F_270,k1_zfmisc_1(k2_zfmisc_1(C_272,D_268)))
      | ~ v1_funct_1(F_270)
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_267)))
      | ~ v1_funct_1(E_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_3373,plain,(
    ! [A_269,B_267,E_271] :
      ( k1_partfun1(A_269,B_267,'#skF_2','#skF_1',E_271,'#skF_4') = k5_relat_1(E_271,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_267)))
      | ~ v1_funct_1(E_271) ) ),
    inference(resolution,[status(thm)],[c_98,c_3360])).

tff(c_3492,plain,(
    ! [A_284,B_285,E_286] :
      ( k1_partfun1(A_284,B_285,'#skF_2','#skF_1',E_286,'#skF_4') = k5_relat_1(E_286,'#skF_4')
      | ~ m1_subset_1(E_286,k1_zfmisc_1(k2_zfmisc_1(A_284,B_285)))
      | ~ v1_funct_1(E_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_3373])).

tff(c_3511,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_3492])).

tff(c_3524,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_3162,c_3511])).

tff(c_44,plain,(
    ! [A_35,B_37] :
      ( v2_funct_1(A_35)
      | k2_relat_1(B_37) != k1_relat_1(A_35)
      | ~ v2_funct_1(k5_relat_1(B_37,A_35))
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3531,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3524,c_44])).

tff(c_3544,plain,
    ( v2_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_102,c_217,c_108,c_112,c_1132,c_3531])).

tff(c_3552,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3544])).

tff(c_301,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_104,c_285])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_305,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_301,c_20])).

tff(c_308,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_305])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_326,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_16])).

tff(c_333,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_326])).

tff(c_1134,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_333])).

tff(c_24,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_117,plain,(
    ! [A_26] : k1_relat_1(k6_partfun1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_24])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( k10_relat_1(A_14,k1_relat_1(B_16)) = k1_relat_1(k5_relat_1(A_14,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1657,plain,(
    ! [B_200,A_201] :
      ( k9_relat_1(B_200,k10_relat_1(B_200,A_201)) = A_201
      | ~ r1_tarski(A_201,k2_relat_1(B_200))
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1659,plain,(
    ! [A_201] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_201)) = A_201
      | ~ r1_tarski(A_201,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_1657])).

tff(c_1678,plain,(
    ! [A_202] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_202)) = A_202
      | ~ r1_tarski(A_202,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_108,c_1659])).

tff(c_1695,plain,(
    ! [B_16] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_16))) = k1_relat_1(B_16)
      | ~ r1_tarski(k1_relat_1(B_16),'#skF_2')
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1678])).

tff(c_1703,plain,(
    ! [B_16] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_16))) = k1_relat_1(B_16)
      | ~ r1_tarski(k1_relat_1(B_16),'#skF_2')
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_1695])).

tff(c_3537,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3524,c_1703])).

tff(c_3548,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_1134,c_117,c_3537])).

tff(c_3553,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_3552,c_3548])).

tff(c_3556,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_3553])).

tff(c_3560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_302,c_3556])).

tff(c_3561,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3544])).

tff(c_30,plain,(
    ! [A_28] :
      ( k5_relat_1(A_28,k6_relat_1(k2_relat_1(A_28))) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_114,plain,(
    ! [A_28] :
      ( k5_relat_1(A_28,k6_partfun1(k2_relat_1(A_28))) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_30])).

tff(c_1150,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_114])).

tff(c_1162,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_1150])).

tff(c_3562,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3544])).

tff(c_54,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k2_funct_1(A_39)) = k6_relat_1(k1_relat_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_110,plain,(
    ! [A_39] :
      ( k5_relat_1(A_39,k2_funct_1(A_39)) = k6_partfun1(k1_relat_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54])).

tff(c_36,plain,(
    ! [A_31] :
      ( v1_relat_1(k2_funct_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_100,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_106,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_255])).

tff(c_685,plain,(
    ! [A_141,B_142,D_143] :
      ( r2_relset_1(A_141,B_142,D_143,D_143)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_696,plain,(
    ! [A_51] : r2_relset_1(A_51,A_51,k6_partfun1(A_51),k6_partfun1(A_51)) ),
    inference(resolution,[status(thm)],[c_109,c_685])).

tff(c_1133,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_1110])).

tff(c_3563,plain,(
    ! [A_287,B_288,C_289,D_290] :
      ( k2_relset_1(A_287,B_288,C_289) = B_288
      | ~ r2_relset_1(B_288,B_288,k1_partfun1(B_288,A_287,A_287,B_288,D_290,C_289),k6_partfun1(B_288))
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(B_288,A_287)))
      | ~ v1_funct_2(D_290,B_288,A_287)
      | ~ v1_funct_1(D_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ v1_funct_2(C_289,A_287,B_288)
      | ~ v1_funct_1(C_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_3566,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3162,c_3563])).

tff(c_3568,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_108,c_106,c_104,c_696,c_1133,c_3566])).

tff(c_52,plain,(
    ! [A_39] :
      ( k5_relat_1(k2_funct_1(A_39),A_39) = k6_relat_1(k2_relat_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_111,plain,(
    ! [A_39] :
      ( k5_relat_1(k2_funct_1(A_39),A_39) = k6_partfun1(k2_relat_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_52])).

tff(c_3639,plain,(
    ! [A_14] :
      ( k1_relat_1(k5_relat_1(A_14,'#skF_4')) = k10_relat_1(A_14,'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3562,c_18])).

tff(c_5187,plain,(
    ! [A_313] :
      ( k1_relat_1(k5_relat_1(A_313,'#skF_4')) = k10_relat_1(A_313,'#skF_2')
      | ~ v1_relat_1(A_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_3639])).

tff(c_5279,plain,
    ( k1_relat_1(k6_partfun1(k2_relat_1('#skF_4'))) = k10_relat_1(k2_funct_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_5187])).

tff(c_5303,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_2') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_102,c_3561,c_3568,c_117,c_5279])).

tff(c_5802,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5303])).

tff(c_5805,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_5802])).

tff(c_5809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_102,c_5805])).

tff(c_5811,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5303])).

tff(c_568,plain,(
    ! [A_134] :
      ( k1_relat_1(k2_funct_1(A_134)) = k2_relat_1(A_134)
      | ~ v2_funct_1(A_134)
      | ~ v1_funct_1(A_134)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_28,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_27)),A_27) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_115,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_27)),A_27) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28])).

tff(c_5038,plain,(
    ! [A_311] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_311)),k2_funct_1(A_311)) = k2_funct_1(A_311)
      | ~ v1_relat_1(k2_funct_1(A_311))
      | ~ v2_funct_1(A_311)
      | ~ v1_funct_1(A_311)
      | ~ v1_relat_1(A_311) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_115])).

tff(c_5069,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3568,c_5038])).

tff(c_5100,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_102,c_3561,c_5069])).

tff(c_6792,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5811,c_5100])).

tff(c_22,plain,(
    ! [A_19,B_23,C_25] :
      ( k5_relat_1(k5_relat_1(A_19,B_23),C_25) = k5_relat_1(A_19,k5_relat_1(B_23,C_25))
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3540,plain,(
    ! [C_25] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_25) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_25))
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3524,c_22])).

tff(c_8825,plain,(
    ! [C_374] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_374) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_374))
      | ~ v1_relat_1(C_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_220,c_3540])).

tff(c_8938,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6792,c_8825])).

tff(c_9019,plain,(
    k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5811,c_8938])).

tff(c_9105,plain,
    ( k5_relat_1('#skF_3',k6_partfun1(k1_relat_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_9019])).

tff(c_9120,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_102,c_3561,c_1162,c_3562,c_9105])).

tff(c_56,plain,(
    ! [A_40] :
      ( k2_funct_1(k2_funct_1(A_40)) = A_40
      | ~ v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_9208,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9120,c_56])).

tff(c_9250,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_102,c_3561,c_9208])).

tff(c_9252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_9250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:22:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.02/3.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.16  
% 9.02/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.16  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.02/3.16  
% 9.02/3.16  %Foreground sorts:
% 9.02/3.16  
% 9.02/3.16  
% 9.02/3.16  %Background operators:
% 9.02/3.16  
% 9.02/3.16  
% 9.02/3.16  %Foreground operators:
% 9.02/3.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.02/3.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.02/3.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.02/3.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.02/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.02/3.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.02/3.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.02/3.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.02/3.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.02/3.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.02/3.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.02/3.16  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.02/3.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.02/3.16  tff('#skF_2', type, '#skF_2': $i).
% 9.02/3.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.02/3.16  tff('#skF_3', type, '#skF_3': $i).
% 9.02/3.16  tff('#skF_1', type, '#skF_1': $i).
% 9.02/3.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.02/3.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.02/3.16  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.02/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.02/3.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.02/3.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.02/3.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.02/3.16  tff('#skF_4', type, '#skF_4': $i).
% 9.02/3.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.02/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.02/3.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.02/3.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.02/3.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.02/3.16  
% 9.02/3.19  tff(f_255, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.02/3.19  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.02/3.19  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.02/3.19  tff(f_164, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.02/3.19  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.02/3.19  tff(f_202, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.02/3.19  tff(f_105, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.02/3.19  tff(f_168, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.02/3.19  tff(f_190, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.02/3.19  tff(f_178, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 9.02/3.19  tff(f_176, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.02/3.19  tff(f_200, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.02/3.19  tff(f_130, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 9.02/3.19  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 9.02/3.19  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 9.02/3.19  tff(f_79, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.02/3.19  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 9.02/3.19  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 9.02/3.19  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 9.02/3.19  tff(f_150, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.02/3.19  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.02/3.19  tff(f_219, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 9.02/3.19  tff(f_140, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.02/3.19  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 9.02/3.19  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 9.02/3.19  tff(f_158, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 9.02/3.19  tff(c_86, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.02/3.19  tff(c_98, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_198, plain, (![B_91, A_92]: (v1_relat_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.02/3.19  tff(c_210, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_98, c_198])).
% 9.02/3.19  tff(c_220, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_210])).
% 9.02/3.19  tff(c_102, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_285, plain, (![C_103, A_104, B_105]: (v4_relat_1(C_103, A_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 9.02/3.19  tff(c_302, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_98, c_285])).
% 9.02/3.19  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.02/3.19  tff(c_104, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_207, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_104, c_198])).
% 9.02/3.19  tff(c_217, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_207])).
% 9.02/3.19  tff(c_108, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_76, plain, (![A_64]: (k6_relat_1(A_64)=k6_partfun1(A_64))), inference(cnfTransformation, [status(thm)], [f_202])).
% 9.02/3.19  tff(c_40, plain, (![A_32]: (v2_funct_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.02/3.19  tff(c_112, plain, (![A_32]: (v2_funct_1(k6_partfun1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_40])).
% 9.02/3.19  tff(c_96, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_1110, plain, (![A_180, B_181, C_182]: (k2_relset_1(A_180, B_181, C_182)=k2_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.02/3.19  tff(c_1123, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_1110])).
% 9.02/3.19  tff(c_1132, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1123])).
% 9.02/3.19  tff(c_70, plain, (![D_55, F_57, B_53, A_52, E_56, C_54]: (m1_subset_1(k1_partfun1(A_52, B_53, C_54, D_55, E_56, F_57), k1_zfmisc_1(k2_zfmisc_1(A_52, D_55))) | ~m1_subset_1(F_57, k1_zfmisc_1(k2_zfmisc_1(C_54, D_55))) | ~v1_funct_1(F_57) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~v1_funct_1(E_56))), inference(cnfTransformation, [status(thm)], [f_190])).
% 9.02/3.19  tff(c_68, plain, (![A_51]: (m1_subset_1(k6_relat_1(A_51), k1_zfmisc_1(k2_zfmisc_1(A_51, A_51))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 9.02/3.19  tff(c_109, plain, (![A_51]: (m1_subset_1(k6_partfun1(A_51), k1_zfmisc_1(k2_zfmisc_1(A_51, A_51))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_68])).
% 9.02/3.19  tff(c_94, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_2613, plain, (![D_225, C_226, A_227, B_228]: (D_225=C_226 | ~r2_relset_1(A_227, B_228, C_226, D_225) | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.02/3.19  tff(c_2627, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_94, c_2613])).
% 9.02/3.19  tff(c_2650, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_2627])).
% 9.02/3.19  tff(c_2840, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2650])).
% 9.02/3.19  tff(c_3154, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2840])).
% 9.02/3.19  tff(c_3161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_104, c_102, c_98, c_3154])).
% 9.02/3.19  tff(c_3162, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2650])).
% 9.02/3.19  tff(c_3360, plain, (![D_268, A_269, B_267, E_271, F_270, C_272]: (k1_partfun1(A_269, B_267, C_272, D_268, E_271, F_270)=k5_relat_1(E_271, F_270) | ~m1_subset_1(F_270, k1_zfmisc_1(k2_zfmisc_1(C_272, D_268))) | ~v1_funct_1(F_270) | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_267))) | ~v1_funct_1(E_271))), inference(cnfTransformation, [status(thm)], [f_200])).
% 9.02/3.19  tff(c_3373, plain, (![A_269, B_267, E_271]: (k1_partfun1(A_269, B_267, '#skF_2', '#skF_1', E_271, '#skF_4')=k5_relat_1(E_271, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_267))) | ~v1_funct_1(E_271))), inference(resolution, [status(thm)], [c_98, c_3360])).
% 9.02/3.19  tff(c_3492, plain, (![A_284, B_285, E_286]: (k1_partfun1(A_284, B_285, '#skF_2', '#skF_1', E_286, '#skF_4')=k5_relat_1(E_286, '#skF_4') | ~m1_subset_1(E_286, k1_zfmisc_1(k2_zfmisc_1(A_284, B_285))) | ~v1_funct_1(E_286))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_3373])).
% 9.02/3.19  tff(c_3511, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_3492])).
% 9.02/3.19  tff(c_3524, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_3162, c_3511])).
% 9.02/3.19  tff(c_44, plain, (![A_35, B_37]: (v2_funct_1(A_35) | k2_relat_1(B_37)!=k1_relat_1(A_35) | ~v2_funct_1(k5_relat_1(B_37, A_35)) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.02/3.19  tff(c_3531, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3524, c_44])).
% 9.02/3.19  tff(c_3544, plain, (v2_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_220, c_102, c_217, c_108, c_112, c_1132, c_3531])).
% 9.02/3.19  tff(c_3552, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_3544])).
% 9.02/3.19  tff(c_301, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_104, c_285])).
% 9.02/3.19  tff(c_20, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.02/3.19  tff(c_305, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_301, c_20])).
% 9.02/3.19  tff(c_308, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_217, c_305])).
% 9.02/3.19  tff(c_16, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.02/3.19  tff(c_326, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_308, c_16])).
% 9.02/3.19  tff(c_333, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_326])).
% 9.02/3.19  tff(c_1134, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_333])).
% 9.02/3.19  tff(c_24, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.02/3.19  tff(c_117, plain, (![A_26]: (k1_relat_1(k6_partfun1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_24])).
% 9.02/3.19  tff(c_18, plain, (![A_14, B_16]: (k10_relat_1(A_14, k1_relat_1(B_16))=k1_relat_1(k5_relat_1(A_14, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.02/3.19  tff(c_1657, plain, (![B_200, A_201]: (k9_relat_1(B_200, k10_relat_1(B_200, A_201))=A_201 | ~r1_tarski(A_201, k2_relat_1(B_200)) | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.02/3.19  tff(c_1659, plain, (![A_201]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_201))=A_201 | ~r1_tarski(A_201, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1132, c_1657])).
% 9.02/3.19  tff(c_1678, plain, (![A_202]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_202))=A_202 | ~r1_tarski(A_202, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_108, c_1659])).
% 9.02/3.19  tff(c_1695, plain, (![B_16]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_16)))=k1_relat_1(B_16) | ~r1_tarski(k1_relat_1(B_16), '#skF_2') | ~v1_relat_1(B_16) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1678])).
% 9.02/3.19  tff(c_1703, plain, (![B_16]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_16)))=k1_relat_1(B_16) | ~r1_tarski(k1_relat_1(B_16), '#skF_2') | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_1695])).
% 9.02/3.19  tff(c_3537, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3524, c_1703])).
% 9.02/3.19  tff(c_3548, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_1134, c_117, c_3537])).
% 9.02/3.19  tff(c_3553, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_3552, c_3548])).
% 9.02/3.19  tff(c_3556, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_3553])).
% 9.02/3.19  tff(c_3560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_302, c_3556])).
% 9.02/3.19  tff(c_3561, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3544])).
% 9.02/3.19  tff(c_30, plain, (![A_28]: (k5_relat_1(A_28, k6_relat_1(k2_relat_1(A_28)))=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.02/3.19  tff(c_114, plain, (![A_28]: (k5_relat_1(A_28, k6_partfun1(k2_relat_1(A_28)))=A_28 | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_30])).
% 9.02/3.19  tff(c_1150, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1132, c_114])).
% 9.02/3.19  tff(c_1162, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_217, c_1150])).
% 9.02/3.19  tff(c_3562, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3544])).
% 9.02/3.19  tff(c_54, plain, (![A_39]: (k5_relat_1(A_39, k2_funct_1(A_39))=k6_relat_1(k1_relat_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.02/3.19  tff(c_110, plain, (![A_39]: (k5_relat_1(A_39, k2_funct_1(A_39))=k6_partfun1(k1_relat_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_54])).
% 9.02/3.19  tff(c_36, plain, (![A_31]: (v1_relat_1(k2_funct_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.02/3.19  tff(c_100, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_106, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_255])).
% 9.02/3.19  tff(c_685, plain, (![A_141, B_142, D_143]: (r2_relset_1(A_141, B_142, D_143, D_143) | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 9.02/3.19  tff(c_696, plain, (![A_51]: (r2_relset_1(A_51, A_51, k6_partfun1(A_51), k6_partfun1(A_51)))), inference(resolution, [status(thm)], [c_109, c_685])).
% 9.02/3.19  tff(c_1133, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_1110])).
% 9.02/3.19  tff(c_3563, plain, (![A_287, B_288, C_289, D_290]: (k2_relset_1(A_287, B_288, C_289)=B_288 | ~r2_relset_1(B_288, B_288, k1_partfun1(B_288, A_287, A_287, B_288, D_290, C_289), k6_partfun1(B_288)) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(B_288, A_287))) | ~v1_funct_2(D_290, B_288, A_287) | ~v1_funct_1(D_290) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~v1_funct_2(C_289, A_287, B_288) | ~v1_funct_1(C_289))), inference(cnfTransformation, [status(thm)], [f_219])).
% 9.02/3.19  tff(c_3566, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3162, c_3563])).
% 9.02/3.19  tff(c_3568, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_108, c_106, c_104, c_696, c_1133, c_3566])).
% 9.02/3.19  tff(c_52, plain, (![A_39]: (k5_relat_1(k2_funct_1(A_39), A_39)=k6_relat_1(k2_relat_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_150])).
% 9.02/3.19  tff(c_111, plain, (![A_39]: (k5_relat_1(k2_funct_1(A_39), A_39)=k6_partfun1(k2_relat_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_52])).
% 9.02/3.19  tff(c_3639, plain, (![A_14]: (k1_relat_1(k5_relat_1(A_14, '#skF_4'))=k10_relat_1(A_14, '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_3562, c_18])).
% 9.02/3.19  tff(c_5187, plain, (![A_313]: (k1_relat_1(k5_relat_1(A_313, '#skF_4'))=k10_relat_1(A_313, '#skF_2') | ~v1_relat_1(A_313))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_3639])).
% 9.02/3.19  tff(c_5279, plain, (k1_relat_1(k6_partfun1(k2_relat_1('#skF_4')))=k10_relat_1(k2_funct_1('#skF_4'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_111, c_5187])).
% 9.02/3.19  tff(c_5303, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_2')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_102, c_3561, c_3568, c_117, c_5279])).
% 9.02/3.19  tff(c_5802, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5303])).
% 9.02/3.19  tff(c_5805, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_5802])).
% 9.02/3.19  tff(c_5809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_102, c_5805])).
% 9.02/3.19  tff(c_5811, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5303])).
% 9.02/3.19  tff(c_568, plain, (![A_134]: (k1_relat_1(k2_funct_1(A_134))=k2_relat_1(A_134) | ~v2_funct_1(A_134) | ~v1_funct_1(A_134) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.02/3.19  tff(c_28, plain, (![A_27]: (k5_relat_1(k6_relat_1(k1_relat_1(A_27)), A_27)=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.02/3.19  tff(c_115, plain, (![A_27]: (k5_relat_1(k6_partfun1(k1_relat_1(A_27)), A_27)=A_27 | ~v1_relat_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_28])).
% 9.02/3.19  tff(c_5038, plain, (![A_311]: (k5_relat_1(k6_partfun1(k2_relat_1(A_311)), k2_funct_1(A_311))=k2_funct_1(A_311) | ~v1_relat_1(k2_funct_1(A_311)) | ~v2_funct_1(A_311) | ~v1_funct_1(A_311) | ~v1_relat_1(A_311))), inference(superposition, [status(thm), theory('equality')], [c_568, c_115])).
% 9.02/3.19  tff(c_5069, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3568, c_5038])).
% 9.02/3.19  tff(c_5100, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_102, c_3561, c_5069])).
% 9.02/3.19  tff(c_6792, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5811, c_5100])).
% 9.02/3.19  tff(c_22, plain, (![A_19, B_23, C_25]: (k5_relat_1(k5_relat_1(A_19, B_23), C_25)=k5_relat_1(A_19, k5_relat_1(B_23, C_25)) | ~v1_relat_1(C_25) | ~v1_relat_1(B_23) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.02/3.19  tff(c_3540, plain, (![C_25]: (k5_relat_1(k6_partfun1('#skF_1'), C_25)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_25)) | ~v1_relat_1(C_25) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3524, c_22])).
% 9.02/3.19  tff(c_8825, plain, (![C_374]: (k5_relat_1(k6_partfun1('#skF_1'), C_374)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_374)) | ~v1_relat_1(C_374))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_220, c_3540])).
% 9.02/3.19  tff(c_8938, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6792, c_8825])).
% 9.02/3.19  tff(c_9019, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5811, c_8938])).
% 9.02/3.19  tff(c_9105, plain, (k5_relat_1('#skF_3', k6_partfun1(k1_relat_1('#skF_4')))=k2_funct_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_110, c_9019])).
% 9.02/3.19  tff(c_9120, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_220, c_102, c_3561, c_1162, c_3562, c_9105])).
% 9.02/3.19  tff(c_56, plain, (![A_40]: (k2_funct_1(k2_funct_1(A_40))=A_40 | ~v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_158])).
% 9.02/3.19  tff(c_9208, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9120, c_56])).
% 9.02/3.19  tff(c_9250, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_220, c_102, c_3561, c_9208])).
% 9.02/3.19  tff(c_9252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_9250])).
% 9.02/3.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.02/3.19  
% 9.02/3.19  Inference rules
% 9.02/3.19  ----------------------
% 9.02/3.19  #Ref     : 0
% 9.02/3.19  #Sup     : 2047
% 9.02/3.19  #Fact    : 0
% 9.02/3.19  #Define  : 0
% 9.02/3.19  #Split   : 15
% 9.02/3.19  #Chain   : 0
% 9.02/3.19  #Close   : 0
% 9.02/3.19  
% 9.02/3.19  Ordering : KBO
% 9.02/3.19  
% 9.02/3.19  Simplification rules
% 9.02/3.19  ----------------------
% 9.02/3.19  #Subsume      : 94
% 9.02/3.19  #Demod        : 2978
% 9.02/3.19  #Tautology    : 875
% 9.02/3.19  #SimpNegUnit  : 8
% 9.02/3.19  #BackRed      : 50
% 9.02/3.19  
% 9.02/3.19  #Partial instantiations: 0
% 9.02/3.19  #Strategies tried      : 1
% 9.02/3.19  
% 9.02/3.19  Timing (in seconds)
% 9.02/3.19  ----------------------
% 9.02/3.19  Preprocessing        : 0.39
% 9.02/3.19  Parsing              : 0.21
% 9.02/3.19  CNF conversion       : 0.03
% 9.02/3.19  Main loop            : 2.03
% 9.02/3.19  Inferencing          : 0.55
% 9.02/3.19  Reduction            : 0.90
% 9.02/3.19  Demodulation         : 0.72
% 9.02/3.19  BG Simplification    : 0.07
% 9.02/3.19  Subsumption          : 0.38
% 9.02/3.19  Abstraction          : 0.07
% 9.02/3.19  MUC search           : 0.00
% 9.02/3.19  Cooper               : 0.00
% 9.02/3.19  Total                : 2.48
% 9.02/3.19  Index Insertion      : 0.00
% 9.02/3.19  Index Deletion       : 0.00
% 9.02/3.19  Index Matching       : 0.00
% 9.02/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
