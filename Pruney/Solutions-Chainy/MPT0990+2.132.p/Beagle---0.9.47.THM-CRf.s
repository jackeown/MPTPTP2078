%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:15 EST 2020

% Result     : Theorem 6.36s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 720 expanded)
%              Number of leaves         :   51 ( 273 expanded)
%              Depth                    :   15
%              Number of atoms          :  410 (2801 expanded)
%              Number of equality atoms :  126 ( 842 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_231,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_170,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_205,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_134,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_158,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_168,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_189,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
           => ( v2_funct_1(C)
              & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_71,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_74,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_155,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_164,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_86,c_155])).

tff(c_173,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_164])).

tff(c_92,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_161,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_155])).

tff(c_170,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_161])).

tff(c_96,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_80,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_202,plain,(
    ! [A_75] :
      ( k4_relat_1(A_75) = k2_funct_1(A_75)
      | ~ v2_funct_1(A_75)
      | ~ v1_funct_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_208,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_202])).

tff(c_214,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_96,c_208])).

tff(c_174,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_185,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_174])).

tff(c_251,plain,(
    ! [B_83,A_84] :
      ( k2_relat_1(B_83) = A_84
      | ~ v2_funct_2(B_83,A_84)
      | ~ v5_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_260,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_185,c_251])).

tff(c_269,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_260])).

tff(c_1897,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_64,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_8,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    ! [A_7] : k1_relat_1(k6_partfun1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_94,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_84,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_2230,plain,(
    ! [B_334,C_335,A_336] :
      ( k6_partfun1(B_334) = k5_relat_1(k2_funct_1(C_335),C_335)
      | k1_xboole_0 = B_334
      | ~ v2_funct_1(C_335)
      | k2_relset_1(A_336,B_334,C_335) != B_334
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_336,B_334)))
      | ~ v1_funct_2(C_335,A_336,B_334)
      | ~ v1_funct_1(C_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_2234,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_2230])).

tff(c_2242,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_2234])).

tff(c_2243,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2242])).

tff(c_24,plain,(
    ! [A_13] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_13),A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2259,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2243,c_24])).

tff(c_2272,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_96,c_80,c_101,c_2259])).

tff(c_50,plain,(
    ! [B_31] :
      ( v2_funct_2(B_31,k2_relat_1(B_31))
      | ~ v5_relat_1(B_31,k2_relat_1(B_31))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2281,plain,
    ( v2_funct_2('#skF_3',k2_relat_1('#skF_3'))
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2272,c_50])).

tff(c_2287,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_185,c_2272,c_2281])).

tff(c_2289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1897,c_2287])).

tff(c_2290,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_90,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_88,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_2302,plain,(
    ! [A_337,B_338,C_339] :
      ( k1_relset_1(A_337,B_338,C_339) = k1_relat_1(C_339)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2315,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_2302])).

tff(c_2377,plain,(
    ! [B_350,A_351,C_352] :
      ( k1_xboole_0 = B_350
      | k1_relset_1(A_351,B_350,C_352) = A_351
      | ~ v1_funct_2(C_352,A_351,B_350)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_351,B_350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2386,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_2377])).

tff(c_2395,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2315,c_2386])).

tff(c_2396,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2395])).

tff(c_186,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_174])).

tff(c_257,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_186,c_251])).

tff(c_266,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_257])).

tff(c_270,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_60,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_240,plain,(
    ! [A_79,B_80,D_81] :
      ( r2_relset_1(A_79,B_80,D_81,D_81)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_247,plain,(
    ! [A_38] : r2_relset_1(A_38,A_38,k6_partfun1(A_38),k6_partfun1(A_38)) ),
    inference(resolution,[status(thm)],[c_60,c_240])).

tff(c_867,plain,(
    ! [B_188,A_187,D_190,C_189,F_191,E_192] :
      ( k1_partfun1(A_187,B_188,C_189,D_190,E_192,F_191) = k5_relat_1(E_192,F_191)
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(C_189,D_190)))
      | ~ v1_funct_1(F_191)
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(E_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_873,plain,(
    ! [A_187,B_188,E_192] :
      ( k1_partfun1(A_187,B_188,'#skF_2','#skF_1',E_192,'#skF_4') = k5_relat_1(E_192,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188)))
      | ~ v1_funct_1(E_192) ) ),
    inference(resolution,[status(thm)],[c_86,c_867])).

tff(c_882,plain,(
    ! [A_194,B_195,E_196] :
      ( k1_partfun1(A_194,B_195,'#skF_2','#skF_1',E_196,'#skF_4') = k5_relat_1(E_196,'#skF_4')
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195)))
      | ~ v1_funct_1(E_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_873])).

tff(c_888,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_882])).

tff(c_895,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_888])).

tff(c_82,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_755,plain,(
    ! [D_166,C_167,A_168,B_169] :
      ( D_166 = C_167
      | ~ r2_relset_1(A_168,B_169,C_167,D_166)
      | ~ m1_subset_1(D_166,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169)))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_763,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_82,c_755])).

tff(c_778,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_763])).

tff(c_779,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_900,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_895,c_779])).

tff(c_1043,plain,(
    ! [E_216,D_221,B_217,A_220,F_218,C_219] :
      ( m1_subset_1(k1_partfun1(A_220,B_217,C_219,D_221,E_216,F_218),k1_zfmisc_1(k2_zfmisc_1(A_220,D_221)))
      | ~ m1_subset_1(F_218,k1_zfmisc_1(k2_zfmisc_1(C_219,D_221)))
      | ~ v1_funct_1(F_218)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_220,B_217)))
      | ~ v1_funct_1(E_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1109,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_895,c_1043])).

tff(c_1138,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_1109])).

tff(c_1140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_900,c_1138])).

tff(c_1141,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_1872,plain,(
    ! [D_270,A_271,B_272,C_273] :
      ( v2_funct_2(D_270,A_271)
      | ~ r2_relset_1(A_271,A_271,k1_partfun1(A_271,B_272,B_272,A_271,C_273,D_270),k6_partfun1(A_271))
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(B_272,A_271)))
      | ~ v1_funct_2(D_270,B_272,A_271)
      | ~ v1_funct_1(D_270)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272)))
      | ~ v1_funct_2(C_273,A_271,B_272)
      | ~ v1_funct_1(C_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1878,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1141,c_1872])).

tff(c_1882,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_90,c_88,c_86,c_247,c_1878])).

tff(c_1884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_1882])).

tff(c_1885,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_26,plain,(
    ! [A_14,B_16] :
      ( k2_funct_1(A_14) = B_16
      | k6_relat_1(k2_relat_1(A_14)) != k5_relat_1(B_16,A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2812,plain,(
    ! [A_409,B_410] :
      ( k2_funct_1(A_409) = B_410
      | k6_partfun1(k2_relat_1(A_409)) != k5_relat_1(B_410,A_409)
      | k2_relat_1(B_410) != k1_relat_1(A_409)
      | ~ v2_funct_1(A_409)
      | ~ v1_funct_1(B_410)
      | ~ v1_relat_1(B_410)
      | ~ v1_funct_1(A_409)
      | ~ v1_relat_1(A_409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_2818,plain,(
    ! [B_410] :
      ( k2_funct_1('#skF_4') = B_410
      | k5_relat_1(B_410,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_410) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_410)
      | ~ v1_relat_1(B_410)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_2812])).

tff(c_2824,plain,(
    ! [B_410] :
      ( k2_funct_1('#skF_4') = B_410
      | k5_relat_1(B_410,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_410) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_410)
      | ~ v1_relat_1(B_410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_2396,c_2818])).

tff(c_2853,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2824])).

tff(c_16,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_98,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16])).

tff(c_2535,plain,(
    ! [B_380,C_381,F_383,A_379,D_382,E_384] :
      ( k1_partfun1(A_379,B_380,C_381,D_382,E_384,F_383) = k5_relat_1(E_384,F_383)
      | ~ m1_subset_1(F_383,k1_zfmisc_1(k2_zfmisc_1(C_381,D_382)))
      | ~ v1_funct_1(F_383)
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380)))
      | ~ v1_funct_1(E_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2541,plain,(
    ! [A_379,B_380,E_384] :
      ( k1_partfun1(A_379,B_380,'#skF_2','#skF_1',E_384,'#skF_4') = k5_relat_1(E_384,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380)))
      | ~ v1_funct_1(E_384) ) ),
    inference(resolution,[status(thm)],[c_86,c_2535])).

tff(c_2642,plain,(
    ! [A_395,B_396,E_397] :
      ( k1_partfun1(A_395,B_396,'#skF_2','#skF_1',E_397,'#skF_4') = k5_relat_1(E_397,'#skF_4')
      | ~ m1_subset_1(E_397,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396)))
      | ~ v1_funct_1(E_397) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2541])).

tff(c_2648,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_2642])).

tff(c_2655,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2648])).

tff(c_2437,plain,(
    ! [D_361,C_362,A_363,B_364] :
      ( D_361 = C_362
      | ~ r2_relset_1(A_363,B_364,C_362,D_361)
      | ~ m1_subset_1(D_361,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364)))
      | ~ m1_subset_1(C_362,k1_zfmisc_1(k2_zfmisc_1(A_363,B_364))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2445,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_82,c_2437])).

tff(c_2460,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2445])).

tff(c_2461,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2460])).

tff(c_2660,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2655,c_2461])).

tff(c_2712,plain,(
    ! [B_404,C_406,F_405,E_403,A_407,D_408] :
      ( m1_subset_1(k1_partfun1(A_407,B_404,C_406,D_408,E_403,F_405),k1_zfmisc_1(k2_zfmisc_1(A_407,D_408)))
      | ~ m1_subset_1(F_405,k1_zfmisc_1(k2_zfmisc_1(C_406,D_408)))
      | ~ v1_funct_1(F_405)
      | ~ m1_subset_1(E_403,k1_zfmisc_1(k2_zfmisc_1(A_407,B_404)))
      | ~ v1_funct_1(E_403) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2770,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2655,c_2712])).

tff(c_2800,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_2770])).

tff(c_2802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2660,c_2800])).

tff(c_2803,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2460])).

tff(c_2928,plain,(
    ! [F_430,A_426,C_428,E_431,D_429,B_427] :
      ( k1_partfun1(A_426,B_427,C_428,D_429,E_431,F_430) = k5_relat_1(E_431,F_430)
      | ~ m1_subset_1(F_430,k1_zfmisc_1(k2_zfmisc_1(C_428,D_429)))
      | ~ v1_funct_1(F_430)
      | ~ m1_subset_1(E_431,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427)))
      | ~ v1_funct_1(E_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_2934,plain,(
    ! [A_426,B_427,E_431] :
      ( k1_partfun1(A_426,B_427,'#skF_2','#skF_1',E_431,'#skF_4') = k5_relat_1(E_431,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_431,k1_zfmisc_1(k2_zfmisc_1(A_426,B_427)))
      | ~ v1_funct_1(E_431) ) ),
    inference(resolution,[status(thm)],[c_86,c_2928])).

tff(c_2943,plain,(
    ! [A_432,B_433,E_434] :
      ( k1_partfun1(A_432,B_433,'#skF_2','#skF_1',E_434,'#skF_4') = k5_relat_1(E_434,'#skF_4')
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433)))
      | ~ v1_funct_1(E_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2934])).

tff(c_2949,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_2943])).

tff(c_2956,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2803,c_2949])).

tff(c_18,plain,(
    ! [A_10,B_12] :
      ( v2_funct_1(A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(k5_relat_1(B_12,A_10))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2963,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2956,c_18])).

tff(c_2970,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_170,c_96,c_98,c_2290,c_2396,c_2963])).

tff(c_2972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2853,c_2970])).

tff(c_2998,plain,(
    ! [B_435] :
      ( k2_funct_1('#skF_4') = B_435
      | k5_relat_1(B_435,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_435) != '#skF_2'
      | ~ v1_funct_1(B_435)
      | ~ v1_relat_1(B_435) ) ),
    inference(splitRight,[status(thm)],[c_2824])).

tff(c_3004,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_2998])).

tff(c_3016,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2290,c_3004])).

tff(c_3034,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3016])).

tff(c_3084,plain,(
    ! [C_448,B_447,E_451,F_450,A_446,D_449] :
      ( k1_partfun1(A_446,B_447,C_448,D_449,E_451,F_450) = k5_relat_1(E_451,F_450)
      | ~ m1_subset_1(F_450,k1_zfmisc_1(k2_zfmisc_1(C_448,D_449)))
      | ~ v1_funct_1(F_450)
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | ~ v1_funct_1(E_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_3090,plain,(
    ! [A_446,B_447,E_451] :
      ( k1_partfun1(A_446,B_447,'#skF_2','#skF_1',E_451,'#skF_4') = k5_relat_1(E_451,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_446,B_447)))
      | ~ v1_funct_1(E_451) ) ),
    inference(resolution,[status(thm)],[c_86,c_3084])).

tff(c_3238,plain,(
    ! [A_467,B_468,E_469] :
      ( k1_partfun1(A_467,B_468,'#skF_2','#skF_1',E_469,'#skF_4') = k5_relat_1(E_469,'#skF_4')
      | ~ m1_subset_1(E_469,k1_zfmisc_1(k2_zfmisc_1(A_467,B_468)))
      | ~ v1_funct_1(E_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3090])).

tff(c_3244,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_3238])).

tff(c_3251,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2803,c_3244])).

tff(c_3253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3034,c_3251])).

tff(c_3254,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3016])).

tff(c_2974,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2824])).

tff(c_12,plain,(
    ! [A_8] :
      ( k4_relat_1(A_8) = k2_funct_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2977,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2974,c_12])).

tff(c_2980,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90,c_2977])).

tff(c_3283,plain,(
    k4_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_2980])).

tff(c_6,plain,(
    ! [A_6] :
      ( k4_relat_1(k4_relat_1(A_6)) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3301,plain,
    ( k4_relat_1('#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3283,c_6])).

tff(c_3305,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_214,c_3301])).

tff(c_3307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.36/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.36/2.33  
% 6.36/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.36/2.34  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.36/2.34  
% 6.36/2.34  %Foreground sorts:
% 6.36/2.34  
% 6.36/2.34  
% 6.36/2.34  %Background operators:
% 6.36/2.34  
% 6.36/2.34  
% 6.36/2.34  %Foreground operators:
% 6.36/2.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.36/2.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.36/2.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.36/2.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.36/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.36/2.34  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.36/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.36/2.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.36/2.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.36/2.34  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.36/2.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.36/2.34  tff('#skF_2', type, '#skF_2': $i).
% 6.36/2.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.36/2.34  tff('#skF_3', type, '#skF_3': $i).
% 6.36/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.36/2.34  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.36/2.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.36/2.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.36/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.36/2.34  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.36/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.36/2.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.36/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.36/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.36/2.34  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.36/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.36/2.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.36/2.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.36/2.34  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.36/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.36/2.34  
% 6.68/2.36  tff(f_231, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.68/2.36  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.68/2.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.68/2.36  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 6.68/2.36  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.68/2.36  tff(f_142, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.68/2.36  tff(f_170, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.68/2.36  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.68/2.36  tff(f_205, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.68/2.36  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 6.68/2.36  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.68/2.36  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.68/2.36  tff(f_158, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.68/2.36  tff(f_116, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.68/2.36  tff(f_168, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.68/2.36  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.68/2.36  tff(f_189, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.68/2.36  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 6.68/2.36  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.68/2.36  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 6.68/2.36  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 6.68/2.36  tff(c_74, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.68/2.36  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_155, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.68/2.36  tff(c_164, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_86, c_155])).
% 6.68/2.36  tff(c_173, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_164])).
% 6.68/2.36  tff(c_92, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_161, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_92, c_155])).
% 6.68/2.36  tff(c_170, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_161])).
% 6.68/2.36  tff(c_96, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_80, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_202, plain, (![A_75]: (k4_relat_1(A_75)=k2_funct_1(A_75) | ~v2_funct_1(A_75) | ~v1_funct_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.68/2.36  tff(c_208, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_202])).
% 6.68/2.36  tff(c_214, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_96, c_208])).
% 6.68/2.36  tff(c_174, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.68/2.36  tff(c_185, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_92, c_174])).
% 6.68/2.36  tff(c_251, plain, (![B_83, A_84]: (k2_relat_1(B_83)=A_84 | ~v2_funct_2(B_83, A_84) | ~v5_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.68/2.36  tff(c_260, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_185, c_251])).
% 6.68/2.36  tff(c_269, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_260])).
% 6.68/2.36  tff(c_1897, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_269])).
% 6.68/2.36  tff(c_64, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.68/2.36  tff(c_8, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.68/2.36  tff(c_101, plain, (![A_7]: (k1_relat_1(k6_partfun1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8])).
% 6.68/2.36  tff(c_76, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_94, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_84, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_2230, plain, (![B_334, C_335, A_336]: (k6_partfun1(B_334)=k5_relat_1(k2_funct_1(C_335), C_335) | k1_xboole_0=B_334 | ~v2_funct_1(C_335) | k2_relset_1(A_336, B_334, C_335)!=B_334 | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_336, B_334))) | ~v1_funct_2(C_335, A_336, B_334) | ~v1_funct_1(C_335))), inference(cnfTransformation, [status(thm)], [f_205])).
% 6.68/2.36  tff(c_2234, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_2230])).
% 6.68/2.36  tff(c_2242, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_2234])).
% 6.68/2.36  tff(c_2243, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_76, c_2242])).
% 6.68/2.36  tff(c_24, plain, (![A_13]: (k1_relat_1(k5_relat_1(k2_funct_1(A_13), A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.68/2.36  tff(c_2259, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2243, c_24])).
% 6.68/2.36  tff(c_2272, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_96, c_80, c_101, c_2259])).
% 6.68/2.36  tff(c_50, plain, (![B_31]: (v2_funct_2(B_31, k2_relat_1(B_31)) | ~v5_relat_1(B_31, k2_relat_1(B_31)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.68/2.36  tff(c_2281, plain, (v2_funct_2('#skF_3', k2_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2272, c_50])).
% 6.68/2.36  tff(c_2287, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_185, c_2272, c_2281])).
% 6.68/2.36  tff(c_2289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1897, c_2287])).
% 6.68/2.36  tff(c_2290, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_269])).
% 6.68/2.36  tff(c_90, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_78, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_88, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_2302, plain, (![A_337, B_338, C_339]: (k1_relset_1(A_337, B_338, C_339)=k1_relat_1(C_339) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.68/2.36  tff(c_2315, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_2302])).
% 6.68/2.36  tff(c_2377, plain, (![B_350, A_351, C_352]: (k1_xboole_0=B_350 | k1_relset_1(A_351, B_350, C_352)=A_351 | ~v1_funct_2(C_352, A_351, B_350) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_351, B_350))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.68/2.36  tff(c_2386, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_2377])).
% 6.68/2.36  tff(c_2395, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2315, c_2386])).
% 6.68/2.36  tff(c_2396, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_78, c_2395])).
% 6.68/2.36  tff(c_186, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_174])).
% 6.68/2.36  tff(c_257, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_186, c_251])).
% 6.68/2.36  tff(c_266, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_257])).
% 6.68/2.36  tff(c_270, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_266])).
% 6.68/2.36  tff(c_60, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.68/2.36  tff(c_240, plain, (![A_79, B_80, D_81]: (r2_relset_1(A_79, B_80, D_81, D_81) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.68/2.36  tff(c_247, plain, (![A_38]: (r2_relset_1(A_38, A_38, k6_partfun1(A_38), k6_partfun1(A_38)))), inference(resolution, [status(thm)], [c_60, c_240])).
% 6.68/2.36  tff(c_867, plain, (![B_188, A_187, D_190, C_189, F_191, E_192]: (k1_partfun1(A_187, B_188, C_189, D_190, E_192, F_191)=k5_relat_1(E_192, F_191) | ~m1_subset_1(F_191, k1_zfmisc_1(k2_zfmisc_1(C_189, D_190))) | ~v1_funct_1(F_191) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(E_192))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.68/2.36  tff(c_873, plain, (![A_187, B_188, E_192]: (k1_partfun1(A_187, B_188, '#skF_2', '#skF_1', E_192, '#skF_4')=k5_relat_1(E_192, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))) | ~v1_funct_1(E_192))), inference(resolution, [status(thm)], [c_86, c_867])).
% 6.68/2.36  tff(c_882, plain, (![A_194, B_195, E_196]: (k1_partfun1(A_194, B_195, '#skF_2', '#skF_1', E_196, '#skF_4')=k5_relat_1(E_196, '#skF_4') | ~m1_subset_1(E_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))) | ~v1_funct_1(E_196))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_873])).
% 6.68/2.36  tff(c_888, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_882])).
% 6.68/2.36  tff(c_895, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_888])).
% 6.68/2.36  tff(c_82, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.68/2.36  tff(c_755, plain, (![D_166, C_167, A_168, B_169]: (D_166=C_167 | ~r2_relset_1(A_168, B_169, C_167, D_166) | ~m1_subset_1(D_166, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.68/2.36  tff(c_763, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_82, c_755])).
% 6.68/2.36  tff(c_778, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_763])).
% 6.68/2.36  tff(c_779, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_778])).
% 6.68/2.36  tff(c_900, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_895, c_779])).
% 6.68/2.36  tff(c_1043, plain, (![E_216, D_221, B_217, A_220, F_218, C_219]: (m1_subset_1(k1_partfun1(A_220, B_217, C_219, D_221, E_216, F_218), k1_zfmisc_1(k2_zfmisc_1(A_220, D_221))) | ~m1_subset_1(F_218, k1_zfmisc_1(k2_zfmisc_1(C_219, D_221))) | ~v1_funct_1(F_218) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_220, B_217))) | ~v1_funct_1(E_216))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.68/2.36  tff(c_1109, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_895, c_1043])).
% 6.68/2.36  tff(c_1138, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_1109])).
% 6.68/2.36  tff(c_1140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_900, c_1138])).
% 6.68/2.36  tff(c_1141, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_778])).
% 6.68/2.36  tff(c_1872, plain, (![D_270, A_271, B_272, C_273]: (v2_funct_2(D_270, A_271) | ~r2_relset_1(A_271, A_271, k1_partfun1(A_271, B_272, B_272, A_271, C_273, D_270), k6_partfun1(A_271)) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(B_272, A_271))) | ~v1_funct_2(D_270, B_272, A_271) | ~v1_funct_1(D_270) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))) | ~v1_funct_2(C_273, A_271, B_272) | ~v1_funct_1(C_273))), inference(cnfTransformation, [status(thm)], [f_189])).
% 6.68/2.36  tff(c_1878, plain, (v2_funct_2('#skF_4', '#skF_1') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1141, c_1872])).
% 6.68/2.36  tff(c_1882, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_90, c_88, c_86, c_247, c_1878])).
% 6.68/2.36  tff(c_1884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_270, c_1882])).
% 6.68/2.36  tff(c_1885, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_266])).
% 6.68/2.36  tff(c_26, plain, (![A_14, B_16]: (k2_funct_1(A_14)=B_16 | k6_relat_1(k2_relat_1(A_14))!=k5_relat_1(B_16, A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.68/2.36  tff(c_2812, plain, (![A_409, B_410]: (k2_funct_1(A_409)=B_410 | k6_partfun1(k2_relat_1(A_409))!=k5_relat_1(B_410, A_409) | k2_relat_1(B_410)!=k1_relat_1(A_409) | ~v2_funct_1(A_409) | ~v1_funct_1(B_410) | ~v1_relat_1(B_410) | ~v1_funct_1(A_409) | ~v1_relat_1(A_409))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26])).
% 6.68/2.36  tff(c_2818, plain, (![B_410]: (k2_funct_1('#skF_4')=B_410 | k5_relat_1(B_410, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_410)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_410) | ~v1_relat_1(B_410) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1885, c_2812])).
% 6.68/2.36  tff(c_2824, plain, (![B_410]: (k2_funct_1('#skF_4')=B_410 | k5_relat_1(B_410, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_410)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_410) | ~v1_relat_1(B_410))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_2396, c_2818])).
% 6.68/2.36  tff(c_2853, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2824])).
% 6.68/2.36  tff(c_16, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.68/2.36  tff(c_98, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16])).
% 6.68/2.36  tff(c_2535, plain, (![B_380, C_381, F_383, A_379, D_382, E_384]: (k1_partfun1(A_379, B_380, C_381, D_382, E_384, F_383)=k5_relat_1(E_384, F_383) | ~m1_subset_1(F_383, k1_zfmisc_1(k2_zfmisc_1(C_381, D_382))) | ~v1_funct_1(F_383) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))) | ~v1_funct_1(E_384))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.68/2.36  tff(c_2541, plain, (![A_379, B_380, E_384]: (k1_partfun1(A_379, B_380, '#skF_2', '#skF_1', E_384, '#skF_4')=k5_relat_1(E_384, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))) | ~v1_funct_1(E_384))), inference(resolution, [status(thm)], [c_86, c_2535])).
% 6.68/2.36  tff(c_2642, plain, (![A_395, B_396, E_397]: (k1_partfun1(A_395, B_396, '#skF_2', '#skF_1', E_397, '#skF_4')=k5_relat_1(E_397, '#skF_4') | ~m1_subset_1(E_397, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))) | ~v1_funct_1(E_397))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2541])).
% 6.68/2.36  tff(c_2648, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_2642])).
% 6.68/2.36  tff(c_2655, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2648])).
% 6.68/2.36  tff(c_2437, plain, (![D_361, C_362, A_363, B_364]: (D_361=C_362 | ~r2_relset_1(A_363, B_364, C_362, D_361) | ~m1_subset_1(D_361, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))) | ~m1_subset_1(C_362, k1_zfmisc_1(k2_zfmisc_1(A_363, B_364))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.68/2.36  tff(c_2445, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_82, c_2437])).
% 6.68/2.36  tff(c_2460, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2445])).
% 6.68/2.36  tff(c_2461, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2460])).
% 6.68/2.36  tff(c_2660, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2655, c_2461])).
% 6.68/2.36  tff(c_2712, plain, (![B_404, C_406, F_405, E_403, A_407, D_408]: (m1_subset_1(k1_partfun1(A_407, B_404, C_406, D_408, E_403, F_405), k1_zfmisc_1(k2_zfmisc_1(A_407, D_408))) | ~m1_subset_1(F_405, k1_zfmisc_1(k2_zfmisc_1(C_406, D_408))) | ~v1_funct_1(F_405) | ~m1_subset_1(E_403, k1_zfmisc_1(k2_zfmisc_1(A_407, B_404))) | ~v1_funct_1(E_403))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.68/2.36  tff(c_2770, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2655, c_2712])).
% 6.68/2.36  tff(c_2800, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_2770])).
% 6.68/2.36  tff(c_2802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2660, c_2800])).
% 6.68/2.36  tff(c_2803, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2460])).
% 6.68/2.36  tff(c_2928, plain, (![F_430, A_426, C_428, E_431, D_429, B_427]: (k1_partfun1(A_426, B_427, C_428, D_429, E_431, F_430)=k5_relat_1(E_431, F_430) | ~m1_subset_1(F_430, k1_zfmisc_1(k2_zfmisc_1(C_428, D_429))) | ~v1_funct_1(F_430) | ~m1_subset_1(E_431, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))) | ~v1_funct_1(E_431))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.68/2.36  tff(c_2934, plain, (![A_426, B_427, E_431]: (k1_partfun1(A_426, B_427, '#skF_2', '#skF_1', E_431, '#skF_4')=k5_relat_1(E_431, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_431, k1_zfmisc_1(k2_zfmisc_1(A_426, B_427))) | ~v1_funct_1(E_431))), inference(resolution, [status(thm)], [c_86, c_2928])).
% 6.68/2.36  tff(c_2943, plain, (![A_432, B_433, E_434]: (k1_partfun1(A_432, B_433, '#skF_2', '#skF_1', E_434, '#skF_4')=k5_relat_1(E_434, '#skF_4') | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(A_432, B_433))) | ~v1_funct_1(E_434))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2934])).
% 6.68/2.36  tff(c_2949, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_2943])).
% 6.68/2.36  tff(c_2956, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2803, c_2949])).
% 6.68/2.36  tff(c_18, plain, (![A_10, B_12]: (v2_funct_1(A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(k5_relat_1(B_12, A_10)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.68/2.36  tff(c_2963, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2956, c_18])).
% 6.68/2.36  tff(c_2970, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_170, c_96, c_98, c_2290, c_2396, c_2963])).
% 6.68/2.36  tff(c_2972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2853, c_2970])).
% 6.68/2.36  tff(c_2998, plain, (![B_435]: (k2_funct_1('#skF_4')=B_435 | k5_relat_1(B_435, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_435)!='#skF_2' | ~v1_funct_1(B_435) | ~v1_relat_1(B_435))), inference(splitRight, [status(thm)], [c_2824])).
% 6.68/2.36  tff(c_3004, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_170, c_2998])).
% 6.68/2.36  tff(c_3016, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2290, c_3004])).
% 6.68/2.36  tff(c_3034, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_3016])).
% 6.68/2.36  tff(c_3084, plain, (![C_448, B_447, E_451, F_450, A_446, D_449]: (k1_partfun1(A_446, B_447, C_448, D_449, E_451, F_450)=k5_relat_1(E_451, F_450) | ~m1_subset_1(F_450, k1_zfmisc_1(k2_zfmisc_1(C_448, D_449))) | ~v1_funct_1(F_450) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | ~v1_funct_1(E_451))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.68/2.36  tff(c_3090, plain, (![A_446, B_447, E_451]: (k1_partfun1(A_446, B_447, '#skF_2', '#skF_1', E_451, '#skF_4')=k5_relat_1(E_451, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_446, B_447))) | ~v1_funct_1(E_451))), inference(resolution, [status(thm)], [c_86, c_3084])).
% 6.68/2.36  tff(c_3238, plain, (![A_467, B_468, E_469]: (k1_partfun1(A_467, B_468, '#skF_2', '#skF_1', E_469, '#skF_4')=k5_relat_1(E_469, '#skF_4') | ~m1_subset_1(E_469, k1_zfmisc_1(k2_zfmisc_1(A_467, B_468))) | ~v1_funct_1(E_469))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3090])).
% 6.68/2.36  tff(c_3244, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_3238])).
% 6.68/2.36  tff(c_3251, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2803, c_3244])).
% 6.68/2.36  tff(c_3253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3034, c_3251])).
% 6.68/2.36  tff(c_3254, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_3016])).
% 6.68/2.36  tff(c_2974, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2824])).
% 6.68/2.36  tff(c_12, plain, (![A_8]: (k4_relat_1(A_8)=k2_funct_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.68/2.36  tff(c_2977, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2974, c_12])).
% 6.68/2.36  tff(c_2980, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_90, c_2977])).
% 6.68/2.36  tff(c_3283, plain, (k4_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_2980])).
% 6.68/2.36  tff(c_6, plain, (![A_6]: (k4_relat_1(k4_relat_1(A_6))=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.68/2.36  tff(c_3301, plain, (k4_relat_1('#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3283, c_6])).
% 6.68/2.36  tff(c_3305, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_214, c_3301])).
% 6.68/2.36  tff(c_3307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3305])).
% 6.68/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.68/2.36  
% 6.68/2.36  Inference rules
% 6.68/2.36  ----------------------
% 6.68/2.36  #Ref     : 0
% 6.68/2.36  #Sup     : 691
% 6.68/2.36  #Fact    : 0
% 6.68/2.36  #Define  : 0
% 6.68/2.36  #Split   : 33
% 6.68/2.36  #Chain   : 0
% 6.68/2.36  #Close   : 0
% 6.68/2.36  
% 6.68/2.36  Ordering : KBO
% 6.68/2.36  
% 6.68/2.36  Simplification rules
% 6.68/2.36  ----------------------
% 6.68/2.36  #Subsume      : 27
% 6.68/2.36  #Demod        : 761
% 6.68/2.36  #Tautology    : 260
% 6.68/2.36  #SimpNegUnit  : 64
% 6.68/2.36  #BackRed      : 40
% 6.68/2.36  
% 6.68/2.36  #Partial instantiations: 0
% 6.68/2.36  #Strategies tried      : 1
% 6.68/2.36  
% 6.68/2.36  Timing (in seconds)
% 6.68/2.36  ----------------------
% 6.68/2.37  Preprocessing        : 0.48
% 6.68/2.37  Parsing              : 0.26
% 6.68/2.37  CNF conversion       : 0.03
% 6.68/2.37  Main loop            : 1.02
% 6.68/2.37  Inferencing          : 0.36
% 6.68/2.37  Reduction            : 0.36
% 6.68/2.37  Demodulation         : 0.25
% 6.68/2.37  BG Simplification    : 0.05
% 6.68/2.37  Subsumption          : 0.17
% 6.68/2.37  Abstraction          : 0.04
% 6.68/2.37  MUC search           : 0.00
% 6.68/2.37  Cooper               : 0.00
% 6.68/2.37  Total                : 1.56
% 6.68/2.37  Index Insertion      : 0.00
% 6.68/2.37  Index Deletion       : 0.00
% 6.68/2.37  Index Matching       : 0.00
% 6.68/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
