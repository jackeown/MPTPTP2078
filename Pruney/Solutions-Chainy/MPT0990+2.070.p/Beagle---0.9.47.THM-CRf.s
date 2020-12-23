%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:06 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 409 expanded)
%              Number of leaves         :   44 ( 165 expanded)
%              Depth                    :   14
%              Number of atoms          :  309 (1687 expanded)
%              Number of equality atoms :  109 ( 574 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_210,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_125,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_184,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_101,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_142,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_168,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_62,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_147,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_160,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_147])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_159,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_147])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_204,plain,(
    ! [A_70] :
      ( k4_relat_1(A_70) = k2_funct_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_210,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_204])).

tff(c_216,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_84,c_210])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_226,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_2])).

tff(c_234,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_226])).

tff(c_46,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [A_10] : k2_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_3502,plain,(
    ! [A_221,C_222,B_223] :
      ( k6_partfun1(A_221) = k5_relat_1(C_222,k2_funct_1(C_222))
      | k1_xboole_0 = B_223
      | ~ v2_funct_1(C_222)
      | k2_relset_1(A_221,B_223,C_222) != B_223
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_221,B_223)))
      | ~ v1_funct_2(C_222,A_221,B_223)
      | ~ v1_funct_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_3506,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3502])).

tff(c_3514,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_3506])).

tff(c_3515,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3514])).

tff(c_28,plain,(
    ! [A_16] :
      ( k2_relat_1(k5_relat_1(A_16,k2_funct_1(A_16))) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3529,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3515,c_28])).

tff(c_3540,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_84,c_68,c_90,c_3529])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_223,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_4])).

tff(c_232,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_223])).

tff(c_3548,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3540,c_232])).

tff(c_16,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k6_relat_1(k2_relat_1(A_12))) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_88,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k6_partfun1(k2_relat_1(A_12))) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_3634,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3548,c_88])).

tff(c_3642,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_3634])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_1974,plain,(
    ! [B_162,C_163,A_164] :
      ( k6_partfun1(B_162) = k5_relat_1(k2_funct_1(C_163),C_163)
      | k1_xboole_0 = B_162
      | ~ v2_funct_1(C_163)
      | k2_relset_1(A_164,B_162,C_163) != B_162
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_162)))
      | ~ v1_funct_2(C_163,A_164,B_162)
      | ~ v1_funct_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1980,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1974])).

tff(c_1990,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_1980])).

tff(c_1991,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1990])).

tff(c_2038,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1991])).

tff(c_38,plain,(
    ! [A_24] : m1_subset_1(k6_relat_1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_85,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_258,plain,(
    ! [A_71,B_72,D_73] :
      ( r2_relset_1(A_71,B_72,D_73,D_73)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_265,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_85,c_258])).

tff(c_1523,plain,(
    ! [A_134,E_138,B_137,D_133,F_136,C_135] :
      ( m1_subset_1(k1_partfun1(A_134,B_137,C_135,D_133,E_138,F_136),k1_zfmisc_1(k2_zfmisc_1(A_134,D_133)))
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_135,D_133)))
      | ~ v1_funct_1(F_136)
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(A_134,B_137)))
      | ~ v1_funct_1(E_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_676,plain,(
    ! [D_90,C_91,A_92,B_93] :
      ( D_90 = C_91
      | ~ r2_relset_1(A_92,B_93,C_91,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_684,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_676])).

tff(c_699,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_684])).

tff(c_852,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_699])).

tff(c_1546,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1523,c_852])).

tff(c_1569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_1546])).

tff(c_1570,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_699])).

tff(c_2637,plain,(
    ! [A_187,B_188,C_189,D_190] :
      ( k2_relset_1(A_187,B_188,C_189) = B_188
      | ~ r2_relset_1(B_188,B_188,k1_partfun1(B_188,A_187,A_187,B_188,D_190,C_189),k6_partfun1(B_188))
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(B_188,A_187)))
      | ~ v1_funct_2(D_190,B_188,A_187)
      | ~ v1_funct_1(D_190)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_2(C_189,A_187,B_188)
      | ~ v1_funct_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2643,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1570,c_2637])).

tff(c_2647,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_84,c_82,c_80,c_265,c_2643])).

tff(c_2649,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2038,c_2647])).

tff(c_2650,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1991])).

tff(c_2656,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2650])).

tff(c_26,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_26])).

tff(c_3340,plain,(
    ! [D_215,A_216,B_217,E_213,C_214] :
      ( k1_xboole_0 = C_214
      | v2_funct_1(E_213)
      | k2_relset_1(A_216,B_217,D_215) != B_217
      | ~ v2_funct_1(k1_partfun1(A_216,B_217,B_217,C_214,D_215,E_213))
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(B_217,C_214)))
      | ~ v1_funct_2(E_213,B_217,C_214)
      | ~ v1_funct_1(E_213)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217)))
      | ~ v1_funct_2(D_215,A_216,B_217)
      | ~ v1_funct_1(D_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_3344,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1570,c_3340])).

tff(c_3349,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_86,c_72,c_3344])).

tff(c_3351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2656,c_66,c_3349])).

tff(c_3353,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2650])).

tff(c_2651,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1991])).

tff(c_3508,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_3502])).

tff(c_3518,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2651,c_3353,c_3508])).

tff(c_3519,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3518])).

tff(c_3584,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3519,c_28])).

tff(c_3595,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_78,c_3353,c_90,c_3584])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_11)),A_11) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_89,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_11)),A_11) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_3612,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3595,c_89])).

tff(c_3622,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_3612])).

tff(c_1889,plain,(
    ! [C_158,A_156,E_155,F_157,D_153,B_154] :
      ( k1_partfun1(A_156,B_154,C_158,D_153,E_155,F_157) = k5_relat_1(E_155,F_157)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(C_158,D_153)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_1(E_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1895,plain,(
    ! [A_156,B_154,E_155] :
      ( k1_partfun1(A_156,B_154,'#skF_2','#skF_1',E_155,'#skF_4') = k5_relat_1(E_155,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_1(E_155) ) ),
    inference(resolution,[status(thm)],[c_74,c_1889])).

tff(c_3389,plain,(
    ! [A_218,B_219,E_220] :
      ( k1_partfun1(A_218,B_219,'#skF_2','#skF_1',E_220,'#skF_4') = k5_relat_1(E_220,'#skF_4')
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_1(E_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1895])).

tff(c_3395,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3389])).

tff(c_3402,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1570,c_3395])).

tff(c_1978,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1974])).

tff(c_1986,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_1978])).

tff(c_1987,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1986])).

tff(c_8,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2002,plain,(
    ! [C_9] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_9)) = k5_relat_1(k6_partfun1('#skF_2'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1987,c_8])).

tff(c_4942,plain,(
    ! [C_263] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_263)) = k5_relat_1(k6_partfun1('#skF_2'),C_263)
      | ~ v1_relat_1(C_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_159,c_2002])).

tff(c_5002,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3402,c_4942])).

tff(c_5038,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_3642,c_3622,c_5002])).

tff(c_5040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_5038])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.46  
% 6.71/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.46  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.71/2.46  
% 6.71/2.46  %Foreground sorts:
% 6.71/2.46  
% 6.71/2.46  
% 6.71/2.46  %Background operators:
% 6.71/2.46  
% 6.71/2.46  
% 6.71/2.46  %Foreground operators:
% 6.71/2.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.71/2.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.71/2.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.71/2.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.71/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.71/2.46  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.71/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.71/2.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.71/2.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.71/2.46  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.71/2.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.71/2.46  tff('#skF_2', type, '#skF_2': $i).
% 6.71/2.46  tff('#skF_3', type, '#skF_3': $i).
% 6.71/2.46  tff('#skF_1', type, '#skF_1': $i).
% 6.71/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.71/2.46  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.71/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.71/2.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.71/2.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.71/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.71/2.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.71/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.71/2.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.71/2.46  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.71/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.71/2.46  
% 6.71/2.48  tff(f_210, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.71/2.48  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.71/2.48  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 6.71/2.48  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 6.71/2.48  tff(f_125, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.71/2.48  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.71/2.48  tff(f_184, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 6.71/2.48  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 6.71/2.48  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 6.71/2.48  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 6.71/2.48  tff(f_101, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.71/2.48  tff(f_99, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.71/2.48  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.71/2.48  tff(f_142, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.71/2.48  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.71/2.48  tff(f_168, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 6.71/2.48  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 6.71/2.48  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.71/2.48  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 6.71/2.48  tff(c_62, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_147, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.71/2.48  tff(c_160, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_147])).
% 6.71/2.48  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_159, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_147])).
% 6.71/2.48  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_204, plain, (![A_70]: (k4_relat_1(A_70)=k2_funct_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.71/2.48  tff(c_210, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_204])).
% 6.71/2.48  tff(c_216, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_84, c_210])).
% 6.71/2.48  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.71/2.48  tff(c_226, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_2])).
% 6.71/2.48  tff(c_234, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_226])).
% 6.71/2.48  tff(c_46, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.71/2.48  tff(c_12, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.71/2.48  tff(c_90, plain, (![A_10]: (k2_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 6.71/2.48  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_3502, plain, (![A_221, C_222, B_223]: (k6_partfun1(A_221)=k5_relat_1(C_222, k2_funct_1(C_222)) | k1_xboole_0=B_223 | ~v2_funct_1(C_222) | k2_relset_1(A_221, B_223, C_222)!=B_223 | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_221, B_223))) | ~v1_funct_2(C_222, A_221, B_223) | ~v1_funct_1(C_222))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.71/2.48  tff(c_3506, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_3502])).
% 6.71/2.48  tff(c_3514, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_3506])).
% 6.71/2.48  tff(c_3515, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_3514])).
% 6.71/2.48  tff(c_28, plain, (![A_16]: (k2_relat_1(k5_relat_1(A_16, k2_funct_1(A_16)))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.71/2.48  tff(c_3529, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3515, c_28])).
% 6.71/2.48  tff(c_3540, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_84, c_68, c_90, c_3529])).
% 6.71/2.48  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.71/2.48  tff(c_223, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_4])).
% 6.71/2.48  tff(c_232, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_223])).
% 6.71/2.48  tff(c_3548, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3540, c_232])).
% 6.71/2.48  tff(c_16, plain, (![A_12]: (k5_relat_1(A_12, k6_relat_1(k2_relat_1(A_12)))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.71/2.48  tff(c_88, plain, (![A_12]: (k5_relat_1(A_12, k6_partfun1(k2_relat_1(A_12)))=A_12 | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 6.71/2.48  tff(c_3634, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3548, c_88])).
% 6.71/2.48  tff(c_3642, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_3634])).
% 6.71/2.48  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_66, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_1974, plain, (![B_162, C_163, A_164]: (k6_partfun1(B_162)=k5_relat_1(k2_funct_1(C_163), C_163) | k1_xboole_0=B_162 | ~v2_funct_1(C_163) | k2_relset_1(A_164, B_162, C_163)!=B_162 | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_162))) | ~v1_funct_2(C_163, A_164, B_162) | ~v1_funct_1(C_163))), inference(cnfTransformation, [status(thm)], [f_184])).
% 6.71/2.48  tff(c_1980, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1974])).
% 6.71/2.48  tff(c_1990, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_1980])).
% 6.71/2.48  tff(c_1991, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_66, c_1990])).
% 6.71/2.48  tff(c_2038, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1991])).
% 6.71/2.48  tff(c_38, plain, (![A_24]: (m1_subset_1(k6_relat_1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.71/2.48  tff(c_85, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38])).
% 6.71/2.48  tff(c_258, plain, (![A_71, B_72, D_73]: (r2_relset_1(A_71, B_72, D_73, D_73) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.71/2.48  tff(c_265, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_85, c_258])).
% 6.71/2.48  tff(c_1523, plain, (![A_134, E_138, B_137, D_133, F_136, C_135]: (m1_subset_1(k1_partfun1(A_134, B_137, C_135, D_133, E_138, F_136), k1_zfmisc_1(k2_zfmisc_1(A_134, D_133))) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_135, D_133))) | ~v1_funct_1(F_136) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(A_134, B_137))) | ~v1_funct_1(E_138))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.71/2.48  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 6.71/2.48  tff(c_676, plain, (![D_90, C_91, A_92, B_93]: (D_90=C_91 | ~r2_relset_1(A_92, B_93, C_91, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.71/2.48  tff(c_684, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_676])).
% 6.71/2.48  tff(c_699, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_684])).
% 6.71/2.48  tff(c_852, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_699])).
% 6.71/2.48  tff(c_1546, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1523, c_852])).
% 6.71/2.48  tff(c_1569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_1546])).
% 6.71/2.48  tff(c_1570, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_699])).
% 6.71/2.48  tff(c_2637, plain, (![A_187, B_188, C_189, D_190]: (k2_relset_1(A_187, B_188, C_189)=B_188 | ~r2_relset_1(B_188, B_188, k1_partfun1(B_188, A_187, A_187, B_188, D_190, C_189), k6_partfun1(B_188)) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(B_188, A_187))) | ~v1_funct_2(D_190, B_188, A_187) | ~v1_funct_1(D_190) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_2(C_189, A_187, B_188) | ~v1_funct_1(C_189))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.71/2.48  tff(c_2643, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1570, c_2637])).
% 6.71/2.48  tff(c_2647, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_84, c_82, c_80, c_265, c_2643])).
% 6.71/2.48  tff(c_2649, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2038, c_2647])).
% 6.71/2.48  tff(c_2650, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1991])).
% 6.71/2.48  tff(c_2656, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2650])).
% 6.71/2.48  tff(c_26, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.71/2.48  tff(c_86, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_26])).
% 6.71/2.48  tff(c_3340, plain, (![D_215, A_216, B_217, E_213, C_214]: (k1_xboole_0=C_214 | v2_funct_1(E_213) | k2_relset_1(A_216, B_217, D_215)!=B_217 | ~v2_funct_1(k1_partfun1(A_216, B_217, B_217, C_214, D_215, E_213)) | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(B_217, C_214))) | ~v1_funct_2(E_213, B_217, C_214) | ~v1_funct_1(E_213) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))) | ~v1_funct_2(D_215, A_216, B_217) | ~v1_funct_1(D_215))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.71/2.48  tff(c_3344, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1570, c_3340])).
% 6.71/2.48  tff(c_3349, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_86, c_72, c_3344])).
% 6.71/2.48  tff(c_3351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2656, c_66, c_3349])).
% 6.71/2.48  tff(c_3353, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2650])).
% 6.71/2.48  tff(c_2651, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1991])).
% 6.71/2.48  tff(c_3508, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_3502])).
% 6.71/2.48  tff(c_3518, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2651, c_3353, c_3508])).
% 6.71/2.48  tff(c_3519, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_3518])).
% 6.71/2.48  tff(c_3584, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3519, c_28])).
% 6.71/2.48  tff(c_3595, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_78, c_3353, c_90, c_3584])).
% 6.71/2.48  tff(c_14, plain, (![A_11]: (k5_relat_1(k6_relat_1(k1_relat_1(A_11)), A_11)=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.71/2.48  tff(c_89, plain, (![A_11]: (k5_relat_1(k6_partfun1(k1_relat_1(A_11)), A_11)=A_11 | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 6.71/2.48  tff(c_3612, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3595, c_89])).
% 6.71/2.48  tff(c_3622, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_3612])).
% 6.71/2.48  tff(c_1889, plain, (![C_158, A_156, E_155, F_157, D_153, B_154]: (k1_partfun1(A_156, B_154, C_158, D_153, E_155, F_157)=k5_relat_1(E_155, F_157) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(C_158, D_153))) | ~v1_funct_1(F_157) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_154))) | ~v1_funct_1(E_155))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.71/2.48  tff(c_1895, plain, (![A_156, B_154, E_155]: (k1_partfun1(A_156, B_154, '#skF_2', '#skF_1', E_155, '#skF_4')=k5_relat_1(E_155, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_154))) | ~v1_funct_1(E_155))), inference(resolution, [status(thm)], [c_74, c_1889])).
% 6.71/2.48  tff(c_3389, plain, (![A_218, B_219, E_220]: (k1_partfun1(A_218, B_219, '#skF_2', '#skF_1', E_220, '#skF_4')=k5_relat_1(E_220, '#skF_4') | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_1(E_220))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1895])).
% 6.71/2.48  tff(c_3395, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_3389])).
% 6.71/2.48  tff(c_3402, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1570, c_3395])).
% 6.71/2.48  tff(c_1978, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1974])).
% 6.71/2.48  tff(c_1986, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_1978])).
% 6.71/2.48  tff(c_1987, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_1986])).
% 6.71/2.48  tff(c_8, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.71/2.48  tff(c_2002, plain, (![C_9]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_9))=k5_relat_1(k6_partfun1('#skF_2'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1987, c_8])).
% 6.71/2.48  tff(c_4942, plain, (![C_263]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_263))=k5_relat_1(k6_partfun1('#skF_2'), C_263) | ~v1_relat_1(C_263))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_159, c_2002])).
% 6.71/2.48  tff(c_5002, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3402, c_4942])).
% 6.71/2.48  tff(c_5038, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_3642, c_3622, c_5002])).
% 6.71/2.48  tff(c_5040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_5038])).
% 6.71/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/2.48  
% 6.71/2.48  Inference rules
% 6.71/2.48  ----------------------
% 6.71/2.48  #Ref     : 0
% 6.71/2.48  #Sup     : 1081
% 6.71/2.48  #Fact    : 0
% 6.71/2.48  #Define  : 0
% 6.71/2.48  #Split   : 13
% 6.71/2.48  #Chain   : 0
% 6.71/2.48  #Close   : 0
% 6.71/2.48  
% 6.71/2.48  Ordering : KBO
% 6.71/2.48  
% 6.71/2.48  Simplification rules
% 6.71/2.48  ----------------------
% 6.71/2.48  #Subsume      : 19
% 6.71/2.48  #Demod        : 1739
% 6.71/2.48  #Tautology    : 540
% 6.71/2.48  #SimpNegUnit  : 38
% 6.71/2.49  #BackRed      : 33
% 6.71/2.49  
% 6.71/2.49  #Partial instantiations: 0
% 6.71/2.49  #Strategies tried      : 1
% 6.71/2.49  
% 6.71/2.49  Timing (in seconds)
% 6.71/2.49  ----------------------
% 6.71/2.49  Preprocessing        : 0.44
% 6.71/2.49  Parsing              : 0.23
% 6.71/2.49  CNF conversion       : 0.03
% 6.71/2.49  Main loop            : 1.18
% 6.71/2.49  Inferencing          : 0.38
% 6.71/2.49  Reduction            : 0.48
% 6.71/2.49  Demodulation         : 0.36
% 6.71/2.49  BG Simplification    : 0.05
% 6.71/2.49  Subsumption          : 0.20
% 6.71/2.49  Abstraction          : 0.06
% 6.71/2.49  MUC search           : 0.00
% 6.71/2.49  Cooper               : 0.00
% 6.71/2.49  Total                : 1.67
% 6.71/2.49  Index Insertion      : 0.00
% 6.71/2.49  Index Deletion       : 0.00
% 6.71/2.49  Index Matching       : 0.00
% 6.71/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
