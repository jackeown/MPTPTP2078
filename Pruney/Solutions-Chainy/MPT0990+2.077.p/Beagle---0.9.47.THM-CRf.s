%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:07 EST 2020

% Result     : Theorem 6.86s
% Output     : CNFRefutation 6.86s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 681 expanded)
%              Number of leaves         :   43 ( 268 expanded)
%              Depth                    :   14
%              Number of atoms          :  418 (3225 expanded)
%              Number of equality atoms :  126 ( 993 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_250,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_208,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_224,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => v2_funct_1(k5_relat_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_1)).

tff(f_147,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_137,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_192,axiom,(
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

tff(f_166,axiom,(
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

tff(f_149,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_107,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_119,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_107])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_80,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_158,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_171,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_158])).

tff(c_836,plain,(
    ! [C_154,A_155,B_156] :
      ( v1_funct_1(k2_funct_1(C_154))
      | k2_relset_1(A_155,B_156,C_154) != B_156
      | ~ v2_funct_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_2(C_154,A_155,B_156)
      | ~ v1_funct_1(C_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_845,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_836])).

tff(c_853,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_171,c_845])).

tff(c_854,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_853])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_86,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_107])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_6,plain,(
    ! [A_2] :
      ( v2_funct_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_1347,plain,(
    ! [C_232,B_233,A_234] :
      ( m1_subset_1(k2_funct_1(C_232),k1_zfmisc_1(k2_zfmisc_1(B_233,A_234)))
      | k2_relset_1(A_234,B_233,C_232) != B_233
      | ~ v2_funct_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_234,B_233)))
      | ~ v1_funct_2(C_232,A_234,B_233)
      | ~ v1_funct_1(C_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_26,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1423,plain,(
    ! [C_237,A_238,B_239] :
      ( v1_relat_1(k2_funct_1(C_237))
      | k2_relset_1(A_238,B_239,C_237) != B_239
      | ~ v2_funct_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_2(C_237,A_238,B_239)
      | ~ v1_funct_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_1347,c_26])).

tff(c_1432,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1423])).

tff(c_1441,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_72,c_76,c_1432])).

tff(c_842,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_836])).

tff(c_850,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_72,c_76,c_842])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_1452,plain,(
    ! [A_240,C_241,B_242] :
      ( k6_partfun1(A_240) = k5_relat_1(C_241,k2_funct_1(C_241))
      | k1_xboole_0 = B_242
      | ~ v2_funct_1(C_241)
      | k2_relset_1(A_240,B_242,C_241) != B_242
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_240,B_242)))
      | ~ v1_funct_2(C_241,A_240,B_242)
      | ~ v1_funct_1(C_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_1458,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1452])).

tff(c_1466,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_1458])).

tff(c_1467,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1466])).

tff(c_12,plain,(
    ! [A_3,B_5] :
      ( v2_funct_1(k5_relat_1(A_3,B_5))
      | ~ v2_funct_1(B_5)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1475,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1467,c_12])).

tff(c_1485,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_88,c_1441,c_850,c_72,c_1475])).

tff(c_1495,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1485])).

tff(c_1520,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1495])).

tff(c_1524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_88,c_72,c_1520])).

tff(c_1525,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1485])).

tff(c_402,plain,(
    ! [B_115,A_116,F_117,D_114,C_119,E_118] :
      ( k1_partfun1(A_116,B_115,C_119,D_114,E_118,F_117) = k5_relat_1(E_118,F_117)
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_119,D_114)))
      | ~ v1_funct_1(F_117)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_408,plain,(
    ! [A_116,B_115,E_118] :
      ( k1_partfun1(A_116,B_115,'#skF_2','#skF_1',E_118,'#skF_4') = k5_relat_1(E_118,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115)))
      | ~ v1_funct_1(E_118) ) ),
    inference(resolution,[status(thm)],[c_78,c_402])).

tff(c_445,plain,(
    ! [A_126,B_127,E_128] :
      ( k1_partfun1(A_126,B_127,'#skF_2','#skF_1',E_128,'#skF_4') = k5_relat_1(E_128,'#skF_4')
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_1(E_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_408])).

tff(c_451,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_445])).

tff(c_458,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_451])).

tff(c_40,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_239,plain,(
    ! [D_79,C_80,A_81,B_82] :
      ( D_79 = C_80
      | ~ r2_relset_1(A_81,B_82,C_80,D_79)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_247,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_239])).

tff(c_262,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_247])).

tff(c_263,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_463,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_263])).

tff(c_754,plain,(
    ! [B_153,D_152,A_148,F_151,E_150,C_149] :
      ( m1_subset_1(k1_partfun1(A_148,B_153,C_149,D_152,E_150,F_151),k1_zfmisc_1(k2_zfmisc_1(A_148,D_152)))
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_149,D_152)))
      | ~ v1_funct_1(F_151)
      | ~ m1_subset_1(E_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_153)))
      | ~ v1_funct_1(E_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_799,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_754])).

tff(c_824,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_799])).

tff(c_826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_463,c_824])).

tff(c_827,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_2266,plain,(
    ! [A_279,E_278,D_281,C_280,B_282] :
      ( k1_xboole_0 = C_280
      | v2_funct_1(E_278)
      | k2_relset_1(A_279,B_282,D_281) != B_282
      | ~ v2_funct_1(k1_partfun1(A_279,B_282,B_282,C_280,D_281,E_278))
      | ~ m1_subset_1(E_278,k1_zfmisc_1(k2_zfmisc_1(B_282,C_280)))
      | ~ v1_funct_2(E_278,B_282,C_280)
      | ~ v1_funct_1(E_278)
      | ~ m1_subset_1(D_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_282)))
      | ~ v1_funct_2(D_281,A_279,B_282)
      | ~ v1_funct_1(D_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2272,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_827,c_2266])).

tff(c_2280,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_1525,c_76,c_2272])).

tff(c_2282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_854,c_70,c_2280])).

tff(c_2284,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_853])).

tff(c_164,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_158])).

tff(c_170,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_164])).

tff(c_2283,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_853])).

tff(c_2285,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2283])).

tff(c_148,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_155,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_40,c_148])).

tff(c_3902,plain,(
    ! [A_409,B_410,C_411,D_412] :
      ( k2_relset_1(A_409,B_410,C_411) = B_410
      | ~ r2_relset_1(B_410,B_410,k1_partfun1(B_410,A_409,A_409,B_410,D_412,C_411),k6_partfun1(B_410))
      | ~ m1_subset_1(D_412,k1_zfmisc_1(k2_zfmisc_1(B_410,A_409)))
      | ~ v1_funct_2(D_412,B_410,A_409)
      | ~ v1_funct_1(D_412)
      | ~ m1_subset_1(C_411,k1_zfmisc_1(k2_zfmisc_1(A_409,B_410)))
      | ~ v1_funct_2(C_411,A_409,B_410)
      | ~ v1_funct_1(C_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3908,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_3902])).

tff(c_3912,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_88,c_86,c_84,c_155,c_171,c_3908])).

tff(c_3914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2285,c_3912])).

tff(c_3916,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2283])).

tff(c_44,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_22,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3975,plain,(
    ! [A_426,B_427] :
      ( k2_funct_1(A_426) = B_427
      | k6_partfun1(k2_relat_1(A_426)) != k5_relat_1(B_427,A_426)
      | k2_relat_1(B_427) != k1_relat_1(A_426)
      | ~ v2_funct_1(A_426)
      | ~ v1_funct_1(B_427)
      | ~ v1_relat_1(B_427)
      | ~ v1_funct_1(A_426)
      | ~ v1_relat_1(A_426) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_3977,plain,(
    ! [B_427] :
      ( k2_funct_1('#skF_4') = B_427
      | k5_relat_1(B_427,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_427) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_427)
      | ~ v1_relat_1(B_427)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3916,c_3975])).

tff(c_4395,plain,(
    ! [B_460] :
      ( k2_funct_1('#skF_4') = B_460
      | k5_relat_1(B_460,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_460) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_460)
      | ~ v1_relat_1(B_460) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_82,c_2284,c_3977])).

tff(c_4404,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_4395])).

tff(c_4414,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_170,c_4404])).

tff(c_4435,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4414])).

tff(c_4846,plain,(
    ! [B_509,C_510,A_511] :
      ( k6_partfun1(B_509) = k5_relat_1(k2_funct_1(C_510),C_510)
      | k1_xboole_0 = B_509
      | ~ v2_funct_1(C_510)
      | k2_relset_1(A_511,B_509,C_510) != B_509
      | ~ m1_subset_1(C_510,k1_zfmisc_1(k2_zfmisc_1(A_511,B_509)))
      | ~ v1_funct_2(C_510,A_511,B_509)
      | ~ v1_funct_1(C_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_4852,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_4846])).

tff(c_4860,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_72,c_4852])).

tff(c_4861,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4860])).

tff(c_18,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_7),A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4874,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4861,c_18])).

tff(c_4886,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_88,c_72,c_170,c_4874])).

tff(c_3917,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3916,c_171])).

tff(c_4988,plain,(
    ! [A_520,C_521,B_522] :
      ( k6_partfun1(A_520) = k5_relat_1(C_521,k2_funct_1(C_521))
      | k1_xboole_0 = B_522
      | ~ v2_funct_1(C_521)
      | k2_relset_1(A_520,B_522,C_521) != B_522
      | ~ m1_subset_1(C_521,k1_zfmisc_1(k2_zfmisc_1(A_520,B_522)))
      | ~ v1_funct_2(C_521,A_520,B_522)
      | ~ v1_funct_1(C_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_4996,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_4988])).

tff(c_5006,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_3917,c_2284,c_4996])).

tff(c_5007,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5006])).

tff(c_14,plain,(
    ! [A_6] :
      ( k2_relat_1(k5_relat_1(A_6,k2_funct_1(A_6))) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5033,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5007,c_14])).

tff(c_5042,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_82,c_2284,c_4886,c_5033])).

tff(c_5044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4435,c_5042])).

tff(c_5045,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4414])).

tff(c_5053,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5045])).

tff(c_5081,plain,(
    ! [E_529,B_526,D_525,A_527,F_528,C_530] :
      ( k1_partfun1(A_527,B_526,C_530,D_525,E_529,F_528) = k5_relat_1(E_529,F_528)
      | ~ m1_subset_1(F_528,k1_zfmisc_1(k2_zfmisc_1(C_530,D_525)))
      | ~ v1_funct_1(F_528)
      | ~ m1_subset_1(E_529,k1_zfmisc_1(k2_zfmisc_1(A_527,B_526)))
      | ~ v1_funct_1(E_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_5087,plain,(
    ! [A_527,B_526,E_529] :
      ( k1_partfun1(A_527,B_526,'#skF_2','#skF_1',E_529,'#skF_4') = k5_relat_1(E_529,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_529,k1_zfmisc_1(k2_zfmisc_1(A_527,B_526)))
      | ~ v1_funct_1(E_529) ) ),
    inference(resolution,[status(thm)],[c_78,c_5081])).

tff(c_5182,plain,(
    ! [A_539,B_540,E_541] :
      ( k1_partfun1(A_539,B_540,'#skF_2','#skF_1',E_541,'#skF_4') = k5_relat_1(E_541,'#skF_4')
      | ~ m1_subset_1(E_541,k1_zfmisc_1(k2_zfmisc_1(A_539,B_540)))
      | ~ v1_funct_1(E_541) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5087])).

tff(c_5191,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_5182])).

tff(c_5199,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_827,c_5191])).

tff(c_5201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5053,c_5199])).

tff(c_5202,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5045])).

tff(c_24,plain,(
    ! [A_11] :
      ( k2_funct_1(k2_funct_1(A_11)) = A_11
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5223,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5202,c_24])).

tff(c_5244,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_82,c_2284,c_5223])).

tff(c_5246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.20/0.35  % DateTime   : Tue Dec  1 20:44:20 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.86/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.47  
% 6.86/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.47  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.86/2.47  
% 6.86/2.47  %Foreground sorts:
% 6.86/2.47  
% 6.86/2.47  
% 6.86/2.47  %Background operators:
% 6.86/2.47  
% 6.86/2.47  
% 6.86/2.47  %Foreground operators:
% 6.86/2.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.86/2.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.86/2.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.86/2.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.86/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.86/2.47  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.86/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.86/2.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.86/2.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.86/2.47  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.86/2.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.86/2.47  tff('#skF_2', type, '#skF_2': $i).
% 6.86/2.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.86/2.47  tff('#skF_3', type, '#skF_3': $i).
% 6.86/2.47  tff('#skF_1', type, '#skF_1': $i).
% 6.86/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.86/2.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.86/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.86/2.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.86/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.86/2.47  tff('#skF_4', type, '#skF_4': $i).
% 6.86/2.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.86/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.86/2.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.86/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.86/2.47  
% 6.86/2.50  tff(f_250, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 6.86/2.50  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.86/2.50  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.86/2.50  tff(f_208, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.86/2.50  tff(f_45, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 6.86/2.50  tff(f_224, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 6.86/2.50  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => v2_funct_1(k5_relat_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_funct_1)).
% 6.86/2.50  tff(f_147, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.86/2.50  tff(f_137, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.86/2.50  tff(f_121, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.86/2.50  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.86/2.50  tff(f_192, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 6.86/2.50  tff(f_166, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.86/2.50  tff(f_149, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.86/2.50  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 6.86/2.50  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 6.86/2.50  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 6.86/2.50  tff(f_105, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 6.86/2.50  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_107, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.86/2.50  tff(c_119, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_107])).
% 6.86/2.50  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_80, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_158, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.86/2.50  tff(c_171, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_158])).
% 6.86/2.50  tff(c_836, plain, (![C_154, A_155, B_156]: (v1_funct_1(k2_funct_1(C_154)) | k2_relset_1(A_155, B_156, C_154)!=B_156 | ~v2_funct_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_2(C_154, A_155, B_156) | ~v1_funct_1(C_154))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.86/2.50  tff(c_845, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_836])).
% 6.86/2.50  tff(c_853, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_171, c_845])).
% 6.86/2.50  tff(c_854, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_853])).
% 6.86/2.50  tff(c_70, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_86, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_107])).
% 6.86/2.50  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_6, plain, (![A_2]: (v2_funct_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.86/2.50  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_1347, plain, (![C_232, B_233, A_234]: (m1_subset_1(k2_funct_1(C_232), k1_zfmisc_1(k2_zfmisc_1(B_233, A_234))) | k2_relset_1(A_234, B_233, C_232)!=B_233 | ~v2_funct_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_234, B_233))) | ~v1_funct_2(C_232, A_234, B_233) | ~v1_funct_1(C_232))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.86/2.50  tff(c_26, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.86/2.50  tff(c_1423, plain, (![C_237, A_238, B_239]: (v1_relat_1(k2_funct_1(C_237)) | k2_relset_1(A_238, B_239, C_237)!=B_239 | ~v2_funct_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_2(C_237, A_238, B_239) | ~v1_funct_1(C_237))), inference(resolution, [status(thm)], [c_1347, c_26])).
% 6.86/2.50  tff(c_1432, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1423])).
% 6.86/2.50  tff(c_1441, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_72, c_76, c_1432])).
% 6.86/2.50  tff(c_842, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_836])).
% 6.86/2.50  tff(c_850, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_72, c_76, c_842])).
% 6.86/2.50  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_1452, plain, (![A_240, C_241, B_242]: (k6_partfun1(A_240)=k5_relat_1(C_241, k2_funct_1(C_241)) | k1_xboole_0=B_242 | ~v2_funct_1(C_241) | k2_relset_1(A_240, B_242, C_241)!=B_242 | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_240, B_242))) | ~v1_funct_2(C_241, A_240, B_242) | ~v1_funct_1(C_241))), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.86/2.50  tff(c_1458, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1452])).
% 6.86/2.50  tff(c_1466, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_1458])).
% 6.86/2.50  tff(c_1467, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_1466])).
% 6.86/2.50  tff(c_12, plain, (![A_3, B_5]: (v2_funct_1(k5_relat_1(A_3, B_5)) | ~v2_funct_1(B_5) | ~v2_funct_1(A_3) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.86/2.50  tff(c_1475, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1467, c_12])).
% 6.86/2.50  tff(c_1485, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_88, c_1441, c_850, c_72, c_1475])).
% 6.86/2.50  tff(c_1495, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1485])).
% 6.86/2.50  tff(c_1520, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1495])).
% 6.86/2.50  tff(c_1524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_88, c_72, c_1520])).
% 6.86/2.50  tff(c_1525, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_1485])).
% 6.86/2.50  tff(c_402, plain, (![B_115, A_116, F_117, D_114, C_119, E_118]: (k1_partfun1(A_116, B_115, C_119, D_114, E_118, F_117)=k5_relat_1(E_118, F_117) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_119, D_114))) | ~v1_funct_1(F_117) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.86/2.50  tff(c_408, plain, (![A_116, B_115, E_118]: (k1_partfun1(A_116, B_115, '#skF_2', '#skF_1', E_118, '#skF_4')=k5_relat_1(E_118, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))) | ~v1_funct_1(E_118))), inference(resolution, [status(thm)], [c_78, c_402])).
% 6.86/2.50  tff(c_445, plain, (![A_126, B_127, E_128]: (k1_partfun1(A_126, B_127, '#skF_2', '#skF_1', E_128, '#skF_4')=k5_relat_1(E_128, '#skF_4') | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_1(E_128))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_408])).
% 6.86/2.50  tff(c_451, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_445])).
% 6.86/2.50  tff(c_458, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_451])).
% 6.86/2.50  tff(c_40, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.86/2.50  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 6.86/2.50  tff(c_239, plain, (![D_79, C_80, A_81, B_82]: (D_79=C_80 | ~r2_relset_1(A_81, B_82, C_80, D_79) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.86/2.50  tff(c_247, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_239])).
% 6.86/2.50  tff(c_262, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_247])).
% 6.86/2.50  tff(c_263, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_262])).
% 6.86/2.50  tff(c_463, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_263])).
% 6.86/2.50  tff(c_754, plain, (![B_153, D_152, A_148, F_151, E_150, C_149]: (m1_subset_1(k1_partfun1(A_148, B_153, C_149, D_152, E_150, F_151), k1_zfmisc_1(k2_zfmisc_1(A_148, D_152))) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(C_149, D_152))) | ~v1_funct_1(F_151) | ~m1_subset_1(E_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_153))) | ~v1_funct_1(E_150))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.86/2.50  tff(c_799, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_458, c_754])).
% 6.86/2.50  tff(c_824, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_799])).
% 6.86/2.50  tff(c_826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_463, c_824])).
% 6.86/2.50  tff(c_827, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_262])).
% 6.86/2.50  tff(c_2266, plain, (![A_279, E_278, D_281, C_280, B_282]: (k1_xboole_0=C_280 | v2_funct_1(E_278) | k2_relset_1(A_279, B_282, D_281)!=B_282 | ~v2_funct_1(k1_partfun1(A_279, B_282, B_282, C_280, D_281, E_278)) | ~m1_subset_1(E_278, k1_zfmisc_1(k2_zfmisc_1(B_282, C_280))) | ~v1_funct_2(E_278, B_282, C_280) | ~v1_funct_1(E_278) | ~m1_subset_1(D_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_282))) | ~v1_funct_2(D_281, A_279, B_282) | ~v1_funct_1(D_281))), inference(cnfTransformation, [status(thm)], [f_192])).
% 6.86/2.50  tff(c_2272, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_827, c_2266])).
% 6.86/2.50  tff(c_2280, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_1525, c_76, c_2272])).
% 6.86/2.50  tff(c_2282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_854, c_70, c_2280])).
% 6.86/2.50  tff(c_2284, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_853])).
% 6.86/2.50  tff(c_164, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_158])).
% 6.86/2.50  tff(c_170, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_164])).
% 6.86/2.50  tff(c_2283, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_853])).
% 6.86/2.50  tff(c_2285, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2283])).
% 6.86/2.50  tff(c_148, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.86/2.50  tff(c_155, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_40, c_148])).
% 6.86/2.50  tff(c_3902, plain, (![A_409, B_410, C_411, D_412]: (k2_relset_1(A_409, B_410, C_411)=B_410 | ~r2_relset_1(B_410, B_410, k1_partfun1(B_410, A_409, A_409, B_410, D_412, C_411), k6_partfun1(B_410)) | ~m1_subset_1(D_412, k1_zfmisc_1(k2_zfmisc_1(B_410, A_409))) | ~v1_funct_2(D_412, B_410, A_409) | ~v1_funct_1(D_412) | ~m1_subset_1(C_411, k1_zfmisc_1(k2_zfmisc_1(A_409, B_410))) | ~v1_funct_2(C_411, A_409, B_410) | ~v1_funct_1(C_411))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.86/2.50  tff(c_3908, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_827, c_3902])).
% 6.86/2.50  tff(c_3912, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_88, c_86, c_84, c_155, c_171, c_3908])).
% 6.86/2.50  tff(c_3914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2285, c_3912])).
% 6.86/2.50  tff(c_3916, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2283])).
% 6.86/2.50  tff(c_44, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.86/2.50  tff(c_22, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.86/2.50  tff(c_3975, plain, (![A_426, B_427]: (k2_funct_1(A_426)=B_427 | k6_partfun1(k2_relat_1(A_426))!=k5_relat_1(B_427, A_426) | k2_relat_1(B_427)!=k1_relat_1(A_426) | ~v2_funct_1(A_426) | ~v1_funct_1(B_427) | ~v1_relat_1(B_427) | ~v1_funct_1(A_426) | ~v1_relat_1(A_426))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22])).
% 6.86/2.50  tff(c_3977, plain, (![B_427]: (k2_funct_1('#skF_4')=B_427 | k5_relat_1(B_427, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_427)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_427) | ~v1_relat_1(B_427) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3916, c_3975])).
% 6.86/2.50  tff(c_4395, plain, (![B_460]: (k2_funct_1('#skF_4')=B_460 | k5_relat_1(B_460, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_460)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_460) | ~v1_relat_1(B_460))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_82, c_2284, c_3977])).
% 6.86/2.50  tff(c_4404, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_118, c_4395])).
% 6.86/2.50  tff(c_4414, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_170, c_4404])).
% 6.86/2.50  tff(c_4435, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_4414])).
% 6.86/2.50  tff(c_4846, plain, (![B_509, C_510, A_511]: (k6_partfun1(B_509)=k5_relat_1(k2_funct_1(C_510), C_510) | k1_xboole_0=B_509 | ~v2_funct_1(C_510) | k2_relset_1(A_511, B_509, C_510)!=B_509 | ~m1_subset_1(C_510, k1_zfmisc_1(k2_zfmisc_1(A_511, B_509))) | ~v1_funct_2(C_510, A_511, B_509) | ~v1_funct_1(C_510))), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.86/2.50  tff(c_4852, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_4846])).
% 6.86/2.50  tff(c_4860, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_72, c_4852])).
% 6.86/2.50  tff(c_4861, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_4860])).
% 6.86/2.50  tff(c_18, plain, (![A_7]: (k2_relat_1(k5_relat_1(k2_funct_1(A_7), A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.86/2.50  tff(c_4874, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4861, c_18])).
% 6.86/2.50  tff(c_4886, plain, (k2_relat_1(k6_partfun1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_88, c_72, c_170, c_4874])).
% 6.86/2.50  tff(c_3917, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3916, c_171])).
% 6.86/2.50  tff(c_4988, plain, (![A_520, C_521, B_522]: (k6_partfun1(A_520)=k5_relat_1(C_521, k2_funct_1(C_521)) | k1_xboole_0=B_522 | ~v2_funct_1(C_521) | k2_relset_1(A_520, B_522, C_521)!=B_522 | ~m1_subset_1(C_521, k1_zfmisc_1(k2_zfmisc_1(A_520, B_522))) | ~v1_funct_2(C_521, A_520, B_522) | ~v1_funct_1(C_521))), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.86/2.50  tff(c_4996, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_4988])).
% 6.86/2.50  tff(c_5006, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_3917, c_2284, c_4996])).
% 6.86/2.50  tff(c_5007, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_5006])).
% 6.86/2.50  tff(c_14, plain, (![A_6]: (k2_relat_1(k5_relat_1(A_6, k2_funct_1(A_6)))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.86/2.50  tff(c_5033, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5007, c_14])).
% 6.86/2.50  tff(c_5042, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_82, c_2284, c_4886, c_5033])).
% 6.86/2.50  tff(c_5044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4435, c_5042])).
% 6.86/2.50  tff(c_5045, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_4414])).
% 6.86/2.50  tff(c_5053, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_5045])).
% 6.86/2.50  tff(c_5081, plain, (![E_529, B_526, D_525, A_527, F_528, C_530]: (k1_partfun1(A_527, B_526, C_530, D_525, E_529, F_528)=k5_relat_1(E_529, F_528) | ~m1_subset_1(F_528, k1_zfmisc_1(k2_zfmisc_1(C_530, D_525))) | ~v1_funct_1(F_528) | ~m1_subset_1(E_529, k1_zfmisc_1(k2_zfmisc_1(A_527, B_526))) | ~v1_funct_1(E_529))), inference(cnfTransformation, [status(thm)], [f_147])).
% 6.86/2.50  tff(c_5087, plain, (![A_527, B_526, E_529]: (k1_partfun1(A_527, B_526, '#skF_2', '#skF_1', E_529, '#skF_4')=k5_relat_1(E_529, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_529, k1_zfmisc_1(k2_zfmisc_1(A_527, B_526))) | ~v1_funct_1(E_529))), inference(resolution, [status(thm)], [c_78, c_5081])).
% 6.86/2.50  tff(c_5182, plain, (![A_539, B_540, E_541]: (k1_partfun1(A_539, B_540, '#skF_2', '#skF_1', E_541, '#skF_4')=k5_relat_1(E_541, '#skF_4') | ~m1_subset_1(E_541, k1_zfmisc_1(k2_zfmisc_1(A_539, B_540))) | ~v1_funct_1(E_541))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_5087])).
% 6.86/2.50  tff(c_5191, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_5182])).
% 6.86/2.50  tff(c_5199, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_827, c_5191])).
% 6.86/2.50  tff(c_5201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5053, c_5199])).
% 6.86/2.50  tff(c_5202, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_5045])).
% 6.86/2.50  tff(c_24, plain, (![A_11]: (k2_funct_1(k2_funct_1(A_11))=A_11 | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.86/2.50  tff(c_5223, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5202, c_24])).
% 6.86/2.50  tff(c_5244, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_82, c_2284, c_5223])).
% 6.86/2.50  tff(c_5246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_5244])).
% 6.86/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.86/2.50  
% 6.86/2.50  Inference rules
% 6.86/2.50  ----------------------
% 6.86/2.50  #Ref     : 0
% 6.86/2.50  #Sup     : 1151
% 6.86/2.50  #Fact    : 0
% 6.86/2.50  #Define  : 0
% 6.86/2.50  #Split   : 46
% 6.86/2.50  #Chain   : 0
% 6.86/2.50  #Close   : 0
% 6.86/2.50  
% 6.86/2.50  Ordering : KBO
% 6.86/2.50  
% 6.86/2.50  Simplification rules
% 6.86/2.50  ----------------------
% 6.86/2.50  #Subsume      : 48
% 6.86/2.50  #Demod        : 1271
% 6.86/2.50  #Tautology    : 309
% 6.86/2.50  #SimpNegUnit  : 82
% 6.86/2.50  #BackRed      : 40
% 6.86/2.50  
% 6.86/2.50  #Partial instantiations: 0
% 6.86/2.50  #Strategies tried      : 1
% 6.86/2.50  
% 6.86/2.50  Timing (in seconds)
% 6.86/2.50  ----------------------
% 6.86/2.50  Preprocessing        : 0.40
% 6.86/2.50  Parsing              : 0.22
% 6.86/2.50  CNF conversion       : 0.03
% 6.86/2.50  Main loop            : 1.28
% 6.86/2.50  Inferencing          : 0.45
% 6.86/2.50  Reduction            : 0.47
% 6.86/2.50  Demodulation         : 0.34
% 6.86/2.50  BG Simplification    : 0.05
% 6.86/2.50  Subsumption          : 0.22
% 6.86/2.50  Abstraction          : 0.06
% 6.86/2.50  MUC search           : 0.00
% 6.86/2.50  Cooper               : 0.00
% 6.86/2.50  Total                : 1.73
% 6.86/2.50  Index Insertion      : 0.00
% 6.86/2.50  Index Deletion       : 0.00
% 6.86/2.50  Index Matching       : 0.00
% 6.86/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
