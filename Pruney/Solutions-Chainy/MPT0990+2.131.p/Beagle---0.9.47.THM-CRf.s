%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:15 EST 2020

% Result     : Theorem 9.80s
% Output     : CNFRefutation 10.03s
% Verified   : 
% Statistics : Number of formulae       :  309 (2246 expanded)
%              Number of leaves         :   51 ( 828 expanded)
%              Depth                    :   17
%              Number of atoms          :  840 (9492 expanded)
%              Number of equality atoms :  240 (2812 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_243,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_158,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_217,axiom,(
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

tff(f_182,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_150,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_180,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_132,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_170,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_201,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_112,axiom,(
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

tff(c_78,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_100,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_143,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_149,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_96,c_143])).

tff(c_158,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_149])).

tff(c_175,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_186,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_175])).

tff(c_222,plain,(
    ! [B_78,A_79] :
      ( k2_relat_1(B_78) = A_79
      | ~ v2_funct_2(B_78,A_79)
      | ~ v5_relat_1(B_78,A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_228,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_186,c_222])).

tff(c_237,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_228])).

tff(c_241,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_90,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_152,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_90,c_143])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_152])).

tff(c_94,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_92,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_2480,plain,(
    ! [C_325,A_326,B_327] :
      ( v1_funct_1(k2_funct_1(C_325))
      | k2_relset_1(A_326,B_327,C_325) != B_327
      | ~ v2_funct_1(C_325)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_2(C_325,A_326,B_327)
      | ~ v1_funct_1(C_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2489,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_2480])).

tff(c_2498,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_2489])).

tff(c_2499,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2498])).

tff(c_66,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_16,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_16])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_1845,plain,(
    ! [A_230,B_231,C_232] :
      ( k1_relset_1(A_230,B_231,C_232) = k1_relat_1(C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1857,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_1845])).

tff(c_1940,plain,(
    ! [B_247,A_248,C_249] :
      ( k1_xboole_0 = B_247
      | k1_relset_1(A_248,B_247,C_249) = A_248
      | ~ v1_funct_2(C_249,A_248,B_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1949,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_1940])).

tff(c_1958,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1857,c_1949])).

tff(c_1959,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1958])).

tff(c_2287,plain,(
    ! [D_308,E_306,A_307,B_311,C_310,F_309] :
      ( k1_partfun1(A_307,B_311,C_310,D_308,E_306,F_309) = k5_relat_1(E_306,F_309)
      | ~ m1_subset_1(F_309,k1_zfmisc_1(k2_zfmisc_1(C_310,D_308)))
      | ~ v1_funct_1(F_309)
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(A_307,B_311)))
      | ~ v1_funct_1(E_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2295,plain,(
    ! [A_307,B_311,E_306] :
      ( k1_partfun1(A_307,B_311,'#skF_2','#skF_1',E_306,'#skF_4') = k5_relat_1(E_306,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_306,k1_zfmisc_1(k2_zfmisc_1(A_307,B_311)))
      | ~ v1_funct_1(E_306) ) ),
    inference(resolution,[status(thm)],[c_90,c_2287])).

tff(c_2336,plain,(
    ! [A_316,B_317,E_318] :
      ( k1_partfun1(A_316,B_317,'#skF_2','#skF_1',E_318,'#skF_4') = k5_relat_1(E_318,'#skF_4')
      | ~ m1_subset_1(E_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ v1_funct_1(E_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2295])).

tff(c_2345,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_2336])).

tff(c_2353,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2345])).

tff(c_42,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_101,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42])).

tff(c_86,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_2005,plain,(
    ! [D_255,C_256,A_257,B_258] :
      ( D_255 = C_256
      | ~ r2_relset_1(A_257,B_258,C_256,D_255)
      | ~ m1_subset_1(D_255,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258)))
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2013,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_2005])).

tff(c_2028,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_2013])).

tff(c_2043,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2028])).

tff(c_2358,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2353,c_2043])).

tff(c_2364,plain,(
    ! [A_319,B_323,F_321,C_324,D_320,E_322] :
      ( m1_subset_1(k1_partfun1(A_319,B_323,C_324,D_320,E_322,F_321),k1_zfmisc_1(k2_zfmisc_1(A_319,D_320)))
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(C_324,D_320)))
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(A_319,B_323)))
      | ~ v1_funct_1(E_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2429,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_2364])).

tff(c_2460,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_2429])).

tff(c_2470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2358,c_2460])).

tff(c_2471,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2028])).

tff(c_2832,plain,(
    ! [D_368,F_369,A_367,B_371,E_366,C_370] :
      ( k1_partfun1(A_367,B_371,C_370,D_368,E_366,F_369) = k5_relat_1(E_366,F_369)
      | ~ m1_subset_1(F_369,k1_zfmisc_1(k2_zfmisc_1(C_370,D_368)))
      | ~ v1_funct_1(F_369)
      | ~ m1_subset_1(E_366,k1_zfmisc_1(k2_zfmisc_1(A_367,B_371)))
      | ~ v1_funct_1(E_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2840,plain,(
    ! [A_367,B_371,E_366] :
      ( k1_partfun1(A_367,B_371,'#skF_2','#skF_1',E_366,'#skF_4') = k5_relat_1(E_366,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_366,k1_zfmisc_1(k2_zfmisc_1(A_367,B_371)))
      | ~ v1_funct_1(E_366) ) ),
    inference(resolution,[status(thm)],[c_90,c_2832])).

tff(c_3954,plain,(
    ! [A_415,B_416,E_417] :
      ( k1_partfun1(A_415,B_416,'#skF_2','#skF_1',E_417,'#skF_4') = k5_relat_1(E_417,'#skF_4')
      | ~ m1_subset_1(E_417,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416)))
      | ~ v1_funct_1(E_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2840])).

tff(c_3972,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_3954])).

tff(c_3987,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2471,c_3972])).

tff(c_18,plain,(
    ! [A_10,B_12] :
      ( v2_funct_1(A_10)
      | k2_relat_1(B_12) != k1_relat_1(A_10)
      | ~ v2_funct_1(k5_relat_1(B_12,A_10))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3994,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3987,c_18])).

tff(c_4001,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_94,c_158,c_100,c_105,c_1959,c_3994])).

tff(c_4002,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2499,c_4001])).

tff(c_98,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_84,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_88,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_2572,plain,(
    ! [C_346,B_347,A_348] :
      ( v1_funct_2(k2_funct_1(C_346),B_347,A_348)
      | k2_relset_1(A_348,B_347,C_346) != B_347
      | ~ v2_funct_1(C_346)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_348,B_347)))
      | ~ v1_funct_2(C_346,A_348,B_347)
      | ~ v1_funct_1(C_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2578,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_2572])).

tff(c_2587,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_88,c_2578])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_1856,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_1845])).

tff(c_1946,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_1940])).

tff(c_1954,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1856,c_1946])).

tff(c_1955,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1954])).

tff(c_22,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_188,plain,(
    ! [A_73] :
      ( k4_relat_1(A_73) = k2_funct_1(A_73)
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_194,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_188])).

tff(c_200,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_100,c_194])).

tff(c_6,plain,(
    ! [A_6] :
      ( k4_relat_1(k4_relat_1(A_6)) = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_206,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_6])).

tff(c_210,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_206])).

tff(c_2486,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_2480])).

tff(c_2495,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_88,c_2486])).

tff(c_26,plain,(
    ! [A_14] :
      ( k5_relat_1(k2_funct_1(A_14),A_14) = k6_relat_1(k2_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_104,plain,(
    ! [A_14] :
      ( k5_relat_1(k2_funct_1(A_14),A_14) = k6_partfun1(k2_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_1974,plain,(
    ! [B_250,A_251] :
      ( v2_funct_1(B_250)
      | k2_relat_1(B_250) != k1_relat_1(A_251)
      | ~ v2_funct_1(k5_relat_1(B_250,A_251))
      | ~ v1_funct_1(B_250)
      | ~ v1_relat_1(B_250)
      | ~ v1_funct_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1980,plain,(
    ! [A_14] :
      ( v2_funct_1(k2_funct_1(A_14))
      | k2_relat_1(k2_funct_1(A_14)) != k1_relat_1(A_14)
      | ~ v2_funct_1(k6_partfun1(k2_relat_1(A_14)))
      | ~ v1_funct_1(k2_funct_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_1974])).

tff(c_2034,plain,(
    ! [A_260] :
      ( v2_funct_1(k2_funct_1(A_260))
      | k2_relat_1(k2_funct_1(A_260)) != k1_relat_1(A_260)
      | ~ v1_funct_1(k2_funct_1(A_260))
      | ~ v1_relat_1(k2_funct_1(A_260))
      | ~ v2_funct_1(A_260)
      | ~ v1_funct_1(A_260)
      | ~ v1_relat_1(A_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1980])).

tff(c_8,plain,(
    ! [A_7] :
      ( k4_relat_1(A_7) = k2_funct_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2518,plain,(
    ! [A_332] :
      ( k4_relat_1(k2_funct_1(A_332)) = k2_funct_1(k2_funct_1(A_332))
      | k2_relat_1(k2_funct_1(A_332)) != k1_relat_1(A_332)
      | ~ v1_funct_1(k2_funct_1(A_332))
      | ~ v1_relat_1(k2_funct_1(A_332))
      | ~ v2_funct_1(A_332)
      | ~ v1_funct_1(A_332)
      | ~ v1_relat_1(A_332) ) ),
    inference(resolution,[status(thm)],[c_2034,c_8])).

tff(c_2698,plain,(
    ! [A_362] :
      ( k4_relat_1(k2_funct_1(A_362)) = k2_funct_1(k2_funct_1(A_362))
      | k2_relat_1(k2_funct_1(A_362)) != k1_relat_1(A_362)
      | ~ v1_funct_1(k2_funct_1(A_362))
      | ~ v2_funct_1(A_362)
      | ~ v1_funct_1(A_362)
      | ~ v1_relat_1(A_362) ) ),
    inference(resolution,[status(thm)],[c_12,c_2518])).

tff(c_2701,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2495,c_2698])).

tff(c_2707,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_100,c_84,c_1955,c_210,c_2701])).

tff(c_2732,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2707])).

tff(c_2735,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2732])).

tff(c_2738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_100,c_84,c_1955,c_2735])).

tff(c_2740,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2707])).

tff(c_1833,plain,(
    ! [A_229] :
      ( k2_relat_1(k2_funct_1(A_229)) = k1_relat_1(A_229)
      | ~ v2_funct_1(A_229)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_56,plain,(
    ! [B_33] :
      ( v2_funct_2(B_33,k2_relat_1(B_33))
      | ~ v5_relat_1(B_33,k2_relat_1(B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1839,plain,(
    ! [A_229] :
      ( v2_funct_2(k2_funct_1(A_229),k2_relat_1(k2_funct_1(A_229)))
      | ~ v5_relat_1(k2_funct_1(A_229),k1_relat_1(A_229))
      | ~ v1_relat_1(k2_funct_1(A_229))
      | ~ v2_funct_1(A_229)
      | ~ v1_funct_1(A_229)
      | ~ v1_relat_1(A_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1833,c_56])).

tff(c_2810,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2740,c_1839])).

tff(c_2825,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_100,c_84,c_1955,c_2810])).

tff(c_2850,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2825])).

tff(c_2853,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_2850])).

tff(c_2857,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_100,c_2853])).

tff(c_2859,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2825])).

tff(c_1984,plain,(
    ! [A_14] :
      ( v2_funct_1(k2_funct_1(A_14))
      | k2_relat_1(k2_funct_1(A_14)) != k1_relat_1(A_14)
      | ~ v1_funct_1(k2_funct_1(A_14))
      | ~ v1_relat_1(k2_funct_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_1980])).

tff(c_2739,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2707])).

tff(c_2768,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2739,c_22])).

tff(c_2797,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2495,c_2768])).

tff(c_3595,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2859,c_2797])).

tff(c_3596,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3595])).

tff(c_3599,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1984,c_3596])).

tff(c_3606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_100,c_84,c_2859,c_2495,c_1955,c_2740,c_3599])).

tff(c_3607,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3595])).

tff(c_2629,plain,(
    ! [C_356,B_357,A_358] :
      ( m1_subset_1(k2_funct_1(C_356),k1_zfmisc_1(k2_zfmisc_1(B_357,A_358)))
      | k2_relset_1(A_358,B_357,C_356) != B_357
      | ~ v2_funct_1(C_356)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_358,B_357)))
      | ~ v1_funct_2(C_356,A_358,B_357)
      | ~ v1_funct_1(C_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_36,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5130,plain,(
    ! [B_454,A_455,C_456] :
      ( k1_relset_1(B_454,A_455,k2_funct_1(C_456)) = k1_relat_1(k2_funct_1(C_456))
      | k2_relset_1(A_455,B_454,C_456) != B_454
      | ~ v2_funct_1(C_456)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(A_455,B_454)))
      | ~ v1_funct_2(C_456,A_455,B_454)
      | ~ v1_funct_1(C_456) ) ),
    inference(resolution,[status(thm)],[c_2629,c_36])).

tff(c_5166,plain,
    ( k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_5130])).

tff(c_5201,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_88,c_3607,c_5166])).

tff(c_54,plain,(
    ! [B_30,A_29,C_31] :
      ( k1_xboole_0 = B_30
      | k1_relset_1(A_29,B_30,C_31) = A_29
      | ~ v1_funct_2(C_31,A_29,B_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_5579,plain,(
    ! [A_463,B_464,C_465] :
      ( k1_xboole_0 = A_463
      | k1_relset_1(B_464,A_463,k2_funct_1(C_465)) = B_464
      | ~ v1_funct_2(k2_funct_1(C_465),B_464,A_463)
      | k2_relset_1(A_463,B_464,C_465) != B_464
      | ~ v2_funct_1(C_465)
      | ~ m1_subset_1(C_465,k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))
      | ~ v1_funct_2(C_465,A_463,B_464)
      | ~ v1_funct_1(C_465) ) ),
    inference(resolution,[status(thm)],[c_2629,c_54])).

tff(c_5621,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_5579])).

tff(c_5672,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_88,c_2587,c_5201,c_5621])).

tff(c_5674,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4002,c_82,c_5672])).

tff(c_5676,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2498])).

tff(c_187,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_175])).

tff(c_231,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_187,c_222])).

tff(c_240,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_231])).

tff(c_242,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_253,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_relset_1(A_82,B_83,D_84,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_260,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_101,c_253])).

tff(c_924,plain,(
    ! [E_162,A_159,B_163,D_160,F_161,C_164] :
      ( m1_subset_1(k1_partfun1(A_159,B_163,C_164,D_160,E_162,F_161),k1_zfmisc_1(k2_zfmisc_1(A_159,D_160)))
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(C_164,D_160)))
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_162,k1_zfmisc_1(k2_zfmisc_1(A_159,B_163)))
      | ~ v1_funct_1(E_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_436,plain,(
    ! [D_112,C_113,A_114,B_115] :
      ( D_112 = C_113
      | ~ r2_relset_1(A_114,B_115,C_113,D_112)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_444,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_436])).

tff(c_459,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_444])).

tff(c_494,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_943,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_924,c_494])).

tff(c_994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_943])).

tff(c_995,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_1786,plain,(
    ! [D_219,A_220,B_221,C_222] :
      ( v2_funct_2(D_219,A_220)
      | ~ r2_relset_1(A_220,A_220,k1_partfun1(A_220,B_221,B_221,A_220,C_222,D_219),k6_partfun1(A_220))
      | ~ m1_subset_1(D_219,k1_zfmisc_1(k2_zfmisc_1(B_221,A_220)))
      | ~ v1_funct_2(D_219,B_221,A_220)
      | ~ v1_funct_1(D_219)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221)))
      | ~ v1_funct_2(C_222,A_220,B_221)
      | ~ v1_funct_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1792,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_995,c_1786])).

tff(c_1797,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_94,c_92,c_90,c_260,c_1792])).

tff(c_1799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_1797])).

tff(c_1800,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_30,plain,(
    ! [A_15,B_17] :
      ( k2_funct_1(A_15) = B_17
      | k6_relat_1(k2_relat_1(A_15)) != k5_relat_1(B_17,A_15)
      | k2_relat_1(B_17) != k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5706,plain,(
    ! [A_468,B_469] :
      ( k2_funct_1(A_468) = B_469
      | k6_partfun1(k2_relat_1(A_468)) != k5_relat_1(B_469,A_468)
      | k2_relat_1(B_469) != k1_relat_1(A_468)
      | ~ v2_funct_1(A_468)
      | ~ v1_funct_1(B_469)
      | ~ v1_relat_1(B_469)
      | ~ v1_funct_1(A_468)
      | ~ v1_relat_1(A_468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_30])).

tff(c_5714,plain,(
    ! [B_469] :
      ( k2_funct_1('#skF_4') = B_469
      | k5_relat_1(B_469,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_469) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_469)
      | ~ v1_relat_1(B_469)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1800,c_5706])).

tff(c_5719,plain,(
    ! [B_470] :
      ( k2_funct_1('#skF_4') = B_470
      | k5_relat_1(B_470,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_470) != '#skF_2'
      | ~ v1_funct_1(B_470)
      | ~ v1_relat_1(B_470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_94,c_5676,c_1959,c_5714])).

tff(c_5725,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_5719])).

tff(c_5740,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5725])).

tff(c_5759,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5740])).

tff(c_5795,plain,(
    ! [C_484,B_485,A_486] :
      ( v1_funct_2(k2_funct_1(C_484),B_485,A_486)
      | k2_relset_1(A_486,B_485,C_484) != B_485
      | ~ v2_funct_1(C_484)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_486,B_485)))
      | ~ v1_funct_2(C_484,A_486,B_485)
      | ~ v1_funct_1(C_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_5801,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_5795])).

tff(c_5810,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_88,c_5801])).

tff(c_5913,plain,(
    ! [C_502,B_503,A_504] :
      ( m1_subset_1(k2_funct_1(C_502),k1_zfmisc_1(k2_zfmisc_1(B_503,A_504)))
      | k2_relset_1(A_504,B_503,C_502) != B_503
      | ~ v2_funct_1(C_502)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_504,B_503)))
      | ~ v1_funct_2(C_502,A_504,B_503)
      | ~ v1_funct_1(C_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_7628,plain,(
    ! [B_562,A_563,C_564] :
      ( k1_relset_1(B_562,A_563,k2_funct_1(C_564)) = k1_relat_1(k2_funct_1(C_564))
      | k2_relset_1(A_563,B_562,C_564) != B_562
      | ~ v2_funct_1(C_564)
      | ~ m1_subset_1(C_564,k1_zfmisc_1(k2_zfmisc_1(A_563,B_562)))
      | ~ v1_funct_2(C_564,A_563,B_562)
      | ~ v1_funct_1(C_564) ) ),
    inference(resolution,[status(thm)],[c_5913,c_36])).

tff(c_7667,plain,
    ( k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_7628])).

tff(c_7705,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_88,c_7667])).

tff(c_8077,plain,(
    ! [A_570,B_571,C_572] :
      ( k1_xboole_0 = A_570
      | k1_relset_1(B_571,A_570,k2_funct_1(C_572)) = B_571
      | ~ v1_funct_2(k2_funct_1(C_572),B_571,A_570)
      | k2_relset_1(A_570,B_571,C_572) != B_571
      | ~ v2_funct_1(C_572)
      | ~ m1_subset_1(C_572,k1_zfmisc_1(k2_zfmisc_1(A_570,B_571)))
      | ~ v1_funct_2(C_572,A_570,B_571)
      | ~ v1_funct_1(C_572) ) ),
    inference(resolution,[status(thm)],[c_5913,c_54])).

tff(c_8122,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_8077])).

tff(c_8177,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_88,c_5810,c_7705,c_8122])).

tff(c_8178,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_8177])).

tff(c_24,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8187,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8178,c_24])).

tff(c_8194,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_100,c_84,c_8187])).

tff(c_8196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5759,c_8194])).

tff(c_8198,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5740])).

tff(c_8204,plain,
    ( v2_funct_2('#skF_3',k2_relat_1('#skF_3'))
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8198,c_56])).

tff(c_8210,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_186,c_8198,c_8204])).

tff(c_8212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_8210])).

tff(c_8213,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_11265,plain,(
    ! [C_924,A_925,B_926] :
      ( v1_funct_1(k2_funct_1(C_924))
      | k2_relset_1(A_925,B_926,C_924) != B_926
      | ~ v2_funct_1(C_924)
      | ~ m1_subset_1(C_924,k1_zfmisc_1(k2_zfmisc_1(A_925,B_926)))
      | ~ v1_funct_2(C_924,A_925,B_926)
      | ~ v1_funct_1(C_924) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_11274,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_11265])).

tff(c_11283,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_11274])).

tff(c_11284,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11283])).

tff(c_11066,plain,(
    ! [A_892,B_893,C_894] :
      ( k1_relset_1(A_892,B_893,C_894) = k1_relat_1(C_894)
      | ~ m1_subset_1(C_894,k1_zfmisc_1(k2_zfmisc_1(A_892,B_893))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_11078,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_11066])).

tff(c_11138,plain,(
    ! [B_905,A_906,C_907] :
      ( k1_xboole_0 = B_905
      | k1_relset_1(A_906,B_905,C_907) = A_906
      | ~ v1_funct_2(C_907,A_906,B_905)
      | ~ m1_subset_1(C_907,k1_zfmisc_1(k2_zfmisc_1(A_906,B_905))) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_11147,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_90,c_11138])).

tff(c_11156,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_11078,c_11147])).

tff(c_11157,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_11156])).

tff(c_11423,plain,(
    ! [C_963,B_964,E_959,D_961,A_960,F_962] :
      ( k1_partfun1(A_960,B_964,C_963,D_961,E_959,F_962) = k5_relat_1(E_959,F_962)
      | ~ m1_subset_1(F_962,k1_zfmisc_1(k2_zfmisc_1(C_963,D_961)))
      | ~ v1_funct_1(F_962)
      | ~ m1_subset_1(E_959,k1_zfmisc_1(k2_zfmisc_1(A_960,B_964)))
      | ~ v1_funct_1(E_959) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_11429,plain,(
    ! [A_960,B_964,E_959] :
      ( k1_partfun1(A_960,B_964,'#skF_2','#skF_1',E_959,'#skF_4') = k5_relat_1(E_959,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_959,k1_zfmisc_1(k2_zfmisc_1(A_960,B_964)))
      | ~ v1_funct_1(E_959) ) ),
    inference(resolution,[status(thm)],[c_90,c_11423])).

tff(c_11465,plain,(
    ! [A_969,B_970,E_971] :
      ( k1_partfun1(A_969,B_970,'#skF_2','#skF_1',E_971,'#skF_4') = k5_relat_1(E_971,'#skF_4')
      | ~ m1_subset_1(E_971,k1_zfmisc_1(k2_zfmisc_1(A_969,B_970)))
      | ~ v1_funct_1(E_971) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_11429])).

tff(c_11471,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_11465])).

tff(c_11478,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_11471])).

tff(c_11227,plain,(
    ! [D_917,C_918,A_919,B_920] :
      ( D_917 = C_918
      | ~ r2_relset_1(A_919,B_920,C_918,D_917)
      | ~ m1_subset_1(D_917,k1_zfmisc_1(k2_zfmisc_1(A_919,B_920)))
      | ~ m1_subset_1(C_918,k1_zfmisc_1(k2_zfmisc_1(A_919,B_920))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_11235,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_11227])).

tff(c_11250,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_11235])).

tff(c_11285,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11250])).

tff(c_11483,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11478,c_11285])).

tff(c_11599,plain,(
    ! [C_985,A_980,E_983,D_981,B_984,F_982] :
      ( m1_subset_1(k1_partfun1(A_980,B_984,C_985,D_981,E_983,F_982),k1_zfmisc_1(k2_zfmisc_1(A_980,D_981)))
      | ~ m1_subset_1(F_982,k1_zfmisc_1(k2_zfmisc_1(C_985,D_981)))
      | ~ v1_funct_1(F_982)
      | ~ m1_subset_1(E_983,k1_zfmisc_1(k2_zfmisc_1(A_980,B_984)))
      | ~ v1_funct_1(E_983) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_11661,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11478,c_11599])).

tff(c_11692,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_11661])).

tff(c_11694,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11483,c_11692])).

tff(c_11695,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_11250])).

tff(c_12012,plain,(
    ! [C_1036,B_1037,D_1034,E_1032,A_1033,F_1035] :
      ( k1_partfun1(A_1033,B_1037,C_1036,D_1034,E_1032,F_1035) = k5_relat_1(E_1032,F_1035)
      | ~ m1_subset_1(F_1035,k1_zfmisc_1(k2_zfmisc_1(C_1036,D_1034)))
      | ~ v1_funct_1(F_1035)
      | ~ m1_subset_1(E_1032,k1_zfmisc_1(k2_zfmisc_1(A_1033,B_1037)))
      | ~ v1_funct_1(E_1032) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_12020,plain,(
    ! [A_1033,B_1037,E_1032] :
      ( k1_partfun1(A_1033,B_1037,'#skF_2','#skF_1',E_1032,'#skF_4') = k5_relat_1(E_1032,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1032,k1_zfmisc_1(k2_zfmisc_1(A_1033,B_1037)))
      | ~ v1_funct_1(E_1032) ) ),
    inference(resolution,[status(thm)],[c_90,c_12012])).

tff(c_12073,plain,(
    ! [A_1042,B_1043,E_1044] :
      ( k1_partfun1(A_1042,B_1043,'#skF_2','#skF_1',E_1044,'#skF_4') = k5_relat_1(E_1044,'#skF_4')
      | ~ m1_subset_1(E_1044,k1_zfmisc_1(k2_zfmisc_1(A_1042,B_1043)))
      | ~ v1_funct_1(E_1044) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_12020])).

tff(c_12082,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_12073])).

tff(c_12090,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_11695,c_12082])).

tff(c_12203,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12090,c_18])).

tff(c_12210,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_94,c_158,c_100,c_105,c_8213,c_11157,c_12203])).

tff(c_12212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11284,c_12210])).

tff(c_12214,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_11283])).

tff(c_8224,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_8248,plain,(
    ! [A_576,B_577,D_578] :
      ( r2_relset_1(A_576,B_577,D_578,D_578)
      | ~ m1_subset_1(D_578,k1_zfmisc_1(k2_zfmisc_1(A_576,B_577))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8255,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_101,c_8248])).

tff(c_9870,plain,(
    ! [A_791,E_790,B_795,C_794,F_793,D_792] :
      ( k1_partfun1(A_791,B_795,C_794,D_792,E_790,F_793) = k5_relat_1(E_790,F_793)
      | ~ m1_subset_1(F_793,k1_zfmisc_1(k2_zfmisc_1(C_794,D_792)))
      | ~ v1_funct_1(F_793)
      | ~ m1_subset_1(E_790,k1_zfmisc_1(k2_zfmisc_1(A_791,B_795)))
      | ~ v1_funct_1(E_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_9878,plain,(
    ! [A_791,B_795,E_790] :
      ( k1_partfun1(A_791,B_795,'#skF_2','#skF_1',E_790,'#skF_4') = k5_relat_1(E_790,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_790,k1_zfmisc_1(k2_zfmisc_1(A_791,B_795)))
      | ~ v1_funct_1(E_790) ) ),
    inference(resolution,[status(thm)],[c_90,c_9870])).

tff(c_9951,plain,(
    ! [A_796,B_797,E_798] :
      ( k1_partfun1(A_796,B_797,'#skF_2','#skF_1',E_798,'#skF_4') = k5_relat_1(E_798,'#skF_4')
      | ~ m1_subset_1(E_798,k1_zfmisc_1(k2_zfmisc_1(A_796,B_797)))
      | ~ v1_funct_1(E_798) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_9878])).

tff(c_9960,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_9951])).

tff(c_9968,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_9960])).

tff(c_8419,plain,(
    ! [D_605,C_606,A_607,B_608] :
      ( D_605 = C_606
      | ~ r2_relset_1(A_607,B_608,C_606,D_605)
      | ~ m1_subset_1(D_605,k1_zfmisc_1(k2_zfmisc_1(A_607,B_608)))
      | ~ m1_subset_1(C_606,k1_zfmisc_1(k2_zfmisc_1(A_607,B_608))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8427,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_86,c_8419])).

tff(c_8442,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_8427])).

tff(c_9388,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_8442])).

tff(c_9973,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9968,c_9388])).

tff(c_9989,plain,(
    ! [F_801,E_802,D_800,A_799,B_803,C_804] :
      ( m1_subset_1(k1_partfun1(A_799,B_803,C_804,D_800,E_802,F_801),k1_zfmisc_1(k2_zfmisc_1(A_799,D_800)))
      | ~ m1_subset_1(F_801,k1_zfmisc_1(k2_zfmisc_1(C_804,D_800)))
      | ~ v1_funct_1(F_801)
      | ~ m1_subset_1(E_802,k1_zfmisc_1(k2_zfmisc_1(A_799,B_803)))
      | ~ v1_funct_1(E_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_10051,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9968,c_9989])).

tff(c_10076,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_10051])).

tff(c_10078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9973,c_10076])).

tff(c_10079,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_8442])).

tff(c_11007,plain,(
    ! [D_881,A_882,B_883,C_884] :
      ( v2_funct_2(D_881,A_882)
      | ~ r2_relset_1(A_882,A_882,k1_partfun1(A_882,B_883,B_883,A_882,C_884,D_881),k6_partfun1(A_882))
      | ~ m1_subset_1(D_881,k1_zfmisc_1(k2_zfmisc_1(B_883,A_882)))
      | ~ v1_funct_2(D_881,B_883,A_882)
      | ~ v1_funct_1(D_881)
      | ~ m1_subset_1(C_884,k1_zfmisc_1(k2_zfmisc_1(A_882,B_883)))
      | ~ v1_funct_2(C_884,A_882,B_883)
      | ~ v1_funct_1(C_884) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_11013,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10079,c_11007])).

tff(c_11017,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_96,c_94,c_92,c_90,c_8255,c_11013])).

tff(c_11019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8224,c_11017])).

tff(c_11020,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_12784,plain,(
    ! [A_1122,B_1123] :
      ( k2_funct_1(A_1122) = B_1123
      | k6_partfun1(k2_relat_1(A_1122)) != k5_relat_1(B_1123,A_1122)
      | k2_relat_1(B_1123) != k1_relat_1(A_1122)
      | ~ v2_funct_1(A_1122)
      | ~ v1_funct_1(B_1123)
      | ~ v1_relat_1(B_1123)
      | ~ v1_funct_1(A_1122)
      | ~ v1_relat_1(A_1122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_30])).

tff(c_12792,plain,(
    ! [B_1123] :
      ( k2_funct_1('#skF_4') = B_1123
      | k5_relat_1(B_1123,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1123) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_1123)
      | ~ v1_relat_1(B_1123)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11020,c_12784])).

tff(c_12801,plain,(
    ! [B_1124] :
      ( k2_funct_1('#skF_4') = B_1124
      | k5_relat_1(B_1124,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_1124) != '#skF_2'
      | ~ v1_funct_1(B_1124)
      | ~ v1_relat_1(B_1124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_94,c_12214,c_11157,c_12792])).

tff(c_12807,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_12801])).

tff(c_12822,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_8213,c_12807])).

tff(c_12826,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12822])).

tff(c_12577,plain,(
    ! [B_1107,D_1104,E_1102,A_1103,C_1106,F_1105] :
      ( k1_partfun1(A_1103,B_1107,C_1106,D_1104,E_1102,F_1105) = k5_relat_1(E_1102,F_1105)
      | ~ m1_subset_1(F_1105,k1_zfmisc_1(k2_zfmisc_1(C_1106,D_1104)))
      | ~ v1_funct_1(F_1105)
      | ~ m1_subset_1(E_1102,k1_zfmisc_1(k2_zfmisc_1(A_1103,B_1107)))
      | ~ v1_funct_1(E_1102) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_12585,plain,(
    ! [A_1103,B_1107,E_1102] :
      ( k1_partfun1(A_1103,B_1107,'#skF_2','#skF_1',E_1102,'#skF_4') = k5_relat_1(E_1102,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1102,k1_zfmisc_1(k2_zfmisc_1(A_1103,B_1107)))
      | ~ v1_funct_1(E_1102) ) ),
    inference(resolution,[status(thm)],[c_90,c_12577])).

tff(c_12626,plain,(
    ! [A_1112,B_1113,E_1114] :
      ( k1_partfun1(A_1112,B_1113,'#skF_2','#skF_1',E_1114,'#skF_4') = k5_relat_1(E_1114,'#skF_4')
      | ~ m1_subset_1(E_1114,k1_zfmisc_1(k2_zfmisc_1(A_1112,B_1113)))
      | ~ v1_funct_1(E_1114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_12585])).

tff(c_12635,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_12626])).

tff(c_12643,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_12635])).

tff(c_12230,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11250])).

tff(c_12648,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12643,c_12230])).

tff(c_12654,plain,(
    ! [C_1120,D_1116,A_1115,E_1118,F_1117,B_1119] :
      ( m1_subset_1(k1_partfun1(A_1115,B_1119,C_1120,D_1116,E_1118,F_1117),k1_zfmisc_1(k2_zfmisc_1(A_1115,D_1116)))
      | ~ m1_subset_1(F_1117,k1_zfmisc_1(k2_zfmisc_1(C_1120,D_1116)))
      | ~ v1_funct_1(F_1117)
      | ~ m1_subset_1(E_1118,k1_zfmisc_1(k2_zfmisc_1(A_1115,B_1119)))
      | ~ v1_funct_1(E_1118) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_12719,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12643,c_12654])).

tff(c_12750,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_96,c_94,c_90,c_12719])).

tff(c_12761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12648,c_12750])).

tff(c_12762,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_11250])).

tff(c_12982,plain,(
    ! [C_1156,B_1157,D_1154,E_1152,F_1155,A_1153] :
      ( k1_partfun1(A_1153,B_1157,C_1156,D_1154,E_1152,F_1155) = k5_relat_1(E_1152,F_1155)
      | ~ m1_subset_1(F_1155,k1_zfmisc_1(k2_zfmisc_1(C_1156,D_1154)))
      | ~ v1_funct_1(F_1155)
      | ~ m1_subset_1(E_1152,k1_zfmisc_1(k2_zfmisc_1(A_1153,B_1157)))
      | ~ v1_funct_1(E_1152) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_12988,plain,(
    ! [A_1153,B_1157,E_1152] :
      ( k1_partfun1(A_1153,B_1157,'#skF_2','#skF_1',E_1152,'#skF_4') = k5_relat_1(E_1152,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1152,k1_zfmisc_1(k2_zfmisc_1(A_1153,B_1157)))
      | ~ v1_funct_1(E_1152) ) ),
    inference(resolution,[status(thm)],[c_90,c_12982])).

tff(c_13110,plain,(
    ! [A_1166,B_1167,E_1168] :
      ( k1_partfun1(A_1166,B_1167,'#skF_2','#skF_1',E_1168,'#skF_4') = k5_relat_1(E_1168,'#skF_4')
      | ~ m1_subset_1(E_1168,k1_zfmisc_1(k2_zfmisc_1(A_1166,B_1167)))
      | ~ v1_funct_1(E_1168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_12988])).

tff(c_13119,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_13110])).

tff(c_13127,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_12762,c_13119])).

tff(c_13129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12826,c_13127])).

tff(c_13130,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12822])).

tff(c_12217,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12214,c_8])).

tff(c_12220,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_94,c_12217])).

tff(c_12224,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12220,c_6])).

tff(c_12228,plain,(
    k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_12224])).

tff(c_13133,plain,(
    k4_relat_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13130,c_12228])).

tff(c_13189,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13133,c_200])).

tff(c_13191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_13189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.80/3.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.82  
% 9.92/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.83  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.92/3.83  
% 9.92/3.83  %Foreground sorts:
% 9.92/3.83  
% 9.92/3.83  
% 9.92/3.83  %Background operators:
% 9.92/3.83  
% 9.92/3.83  
% 9.92/3.83  %Foreground operators:
% 9.92/3.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.92/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.92/3.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.92/3.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.92/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.92/3.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.92/3.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.92/3.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.92/3.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.92/3.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.92/3.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.92/3.83  tff('#skF_2', type, '#skF_2': $i).
% 9.92/3.83  tff('#skF_3', type, '#skF_3': $i).
% 9.92/3.83  tff('#skF_1', type, '#skF_1': $i).
% 9.92/3.83  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.92/3.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.92/3.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.92/3.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.92/3.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.92/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.92/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.92/3.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.92/3.83  tff('#skF_4', type, '#skF_4': $i).
% 9.92/3.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.92/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.92/3.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.92/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.92/3.83  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 9.92/3.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.92/3.83  
% 10.03/3.87  tff(f_243, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 10.03/3.87  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.03/3.87  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.03/3.87  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.03/3.87  tff(f_158, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 10.03/3.87  tff(f_217, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 10.03/3.87  tff(f_182, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.03/3.87  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 10.03/3.87  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.03/3.87  tff(f_150, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.03/3.87  tff(f_180, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.03/3.87  tff(f_132, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 10.03/3.87  tff(f_130, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.03/3.87  tff(f_170, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.03/3.87  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 10.03/3.87  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.03/3.87  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.03/3.87  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 10.03/3.87  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 10.03/3.87  tff(f_95, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 10.03/3.87  tff(f_201, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 10.03/3.87  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 10.03/3.87  tff(c_78, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_100, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.03/3.87  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_143, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.03/3.87  tff(c_149, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_96, c_143])).
% 10.03/3.87  tff(c_158, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_149])).
% 10.03/3.87  tff(c_175, plain, (![C_70, B_71, A_72]: (v5_relat_1(C_70, B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 10.03/3.87  tff(c_186, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_175])).
% 10.03/3.87  tff(c_222, plain, (![B_78, A_79]: (k2_relat_1(B_78)=A_79 | ~v2_funct_2(B_78, A_79) | ~v5_relat_1(B_78, A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.03/3.87  tff(c_228, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_186, c_222])).
% 10.03/3.87  tff(c_237, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_228])).
% 10.03/3.87  tff(c_241, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_237])).
% 10.03/3.87  tff(c_90, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_152, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_90, c_143])).
% 10.03/3.87  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_152])).
% 10.03/3.87  tff(c_94, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_92, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_2480, plain, (![C_325, A_326, B_327]: (v1_funct_1(k2_funct_1(C_325)) | k2_relset_1(A_326, B_327, C_325)!=B_327 | ~v2_funct_1(C_325) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_2(C_325, A_326, B_327) | ~v1_funct_1(C_325))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.03/3.87  tff(c_2489, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_2480])).
% 10.03/3.87  tff(c_2498, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_2489])).
% 10.03/3.87  tff(c_2499, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2498])).
% 10.03/3.87  tff(c_66, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_182])).
% 10.03/3.87  tff(c_16, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.03/3.87  tff(c_105, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_16])).
% 10.03/3.87  tff(c_82, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_1845, plain, (![A_230, B_231, C_232]: (k1_relset_1(A_230, B_231, C_232)=k1_relat_1(C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.03/3.87  tff(c_1857, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_1845])).
% 10.03/3.87  tff(c_1940, plain, (![B_247, A_248, C_249]: (k1_xboole_0=B_247 | k1_relset_1(A_248, B_247, C_249)=A_248 | ~v1_funct_2(C_249, A_248, B_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.03/3.87  tff(c_1949, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_90, c_1940])).
% 10.03/3.87  tff(c_1958, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1857, c_1949])).
% 10.03/3.87  tff(c_1959, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_1958])).
% 10.03/3.87  tff(c_2287, plain, (![D_308, E_306, A_307, B_311, C_310, F_309]: (k1_partfun1(A_307, B_311, C_310, D_308, E_306, F_309)=k5_relat_1(E_306, F_309) | ~m1_subset_1(F_309, k1_zfmisc_1(k2_zfmisc_1(C_310, D_308))) | ~v1_funct_1(F_309) | ~m1_subset_1(E_306, k1_zfmisc_1(k2_zfmisc_1(A_307, B_311))) | ~v1_funct_1(E_306))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.03/3.87  tff(c_2295, plain, (![A_307, B_311, E_306]: (k1_partfun1(A_307, B_311, '#skF_2', '#skF_1', E_306, '#skF_4')=k5_relat_1(E_306, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_306, k1_zfmisc_1(k2_zfmisc_1(A_307, B_311))) | ~v1_funct_1(E_306))), inference(resolution, [status(thm)], [c_90, c_2287])).
% 10.03/3.87  tff(c_2336, plain, (![A_316, B_317, E_318]: (k1_partfun1(A_316, B_317, '#skF_2', '#skF_1', E_318, '#skF_4')=k5_relat_1(E_318, '#skF_4') | ~m1_subset_1(E_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))) | ~v1_funct_1(E_318))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2295])).
% 10.03/3.87  tff(c_2345, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_2336])).
% 10.03/3.87  tff(c_2353, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2345])).
% 10.03/3.87  tff(c_42, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.03/3.87  tff(c_101, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42])).
% 10.03/3.87  tff(c_86, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_2005, plain, (![D_255, C_256, A_257, B_258]: (D_255=C_256 | ~r2_relset_1(A_257, B_258, C_256, D_255) | ~m1_subset_1(D_255, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.03/3.87  tff(c_2013, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_2005])).
% 10.03/3.87  tff(c_2028, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_2013])).
% 10.03/3.87  tff(c_2043, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2028])).
% 10.03/3.87  tff(c_2358, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2353, c_2043])).
% 10.03/3.87  tff(c_2364, plain, (![A_319, B_323, F_321, C_324, D_320, E_322]: (m1_subset_1(k1_partfun1(A_319, B_323, C_324, D_320, E_322, F_321), k1_zfmisc_1(k2_zfmisc_1(A_319, D_320))) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(C_324, D_320))) | ~v1_funct_1(F_321) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(A_319, B_323))) | ~v1_funct_1(E_322))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.03/3.87  tff(c_2429, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2353, c_2364])).
% 10.03/3.87  tff(c_2460, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_2429])).
% 10.03/3.87  tff(c_2470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2358, c_2460])).
% 10.03/3.87  tff(c_2471, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2028])).
% 10.03/3.87  tff(c_2832, plain, (![D_368, F_369, A_367, B_371, E_366, C_370]: (k1_partfun1(A_367, B_371, C_370, D_368, E_366, F_369)=k5_relat_1(E_366, F_369) | ~m1_subset_1(F_369, k1_zfmisc_1(k2_zfmisc_1(C_370, D_368))) | ~v1_funct_1(F_369) | ~m1_subset_1(E_366, k1_zfmisc_1(k2_zfmisc_1(A_367, B_371))) | ~v1_funct_1(E_366))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.03/3.87  tff(c_2840, plain, (![A_367, B_371, E_366]: (k1_partfun1(A_367, B_371, '#skF_2', '#skF_1', E_366, '#skF_4')=k5_relat_1(E_366, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_366, k1_zfmisc_1(k2_zfmisc_1(A_367, B_371))) | ~v1_funct_1(E_366))), inference(resolution, [status(thm)], [c_90, c_2832])).
% 10.03/3.87  tff(c_3954, plain, (![A_415, B_416, E_417]: (k1_partfun1(A_415, B_416, '#skF_2', '#skF_1', E_417, '#skF_4')=k5_relat_1(E_417, '#skF_4') | ~m1_subset_1(E_417, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))) | ~v1_funct_1(E_417))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2840])).
% 10.03/3.87  tff(c_3972, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_3954])).
% 10.03/3.87  tff(c_3987, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_2471, c_3972])).
% 10.03/3.87  tff(c_18, plain, (![A_10, B_12]: (v2_funct_1(A_10) | k2_relat_1(B_12)!=k1_relat_1(A_10) | ~v2_funct_1(k5_relat_1(B_12, A_10)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.03/3.87  tff(c_3994, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3987, c_18])).
% 10.03/3.87  tff(c_4001, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_94, c_158, c_100, c_105, c_1959, c_3994])).
% 10.03/3.87  tff(c_4002, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2499, c_4001])).
% 10.03/3.87  tff(c_98, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_84, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_88, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_2572, plain, (![C_346, B_347, A_348]: (v1_funct_2(k2_funct_1(C_346), B_347, A_348) | k2_relset_1(A_348, B_347, C_346)!=B_347 | ~v2_funct_1(C_346) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_348, B_347))) | ~v1_funct_2(C_346, A_348, B_347) | ~v1_funct_1(C_346))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.03/3.87  tff(c_2578, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_2572])).
% 10.03/3.87  tff(c_2587, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_88, c_2578])).
% 10.03/3.87  tff(c_12, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.03/3.87  tff(c_80, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_243])).
% 10.03/3.87  tff(c_1856, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_1845])).
% 10.03/3.87  tff(c_1946, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_1940])).
% 10.03/3.87  tff(c_1954, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1856, c_1946])).
% 10.03/3.87  tff(c_1955, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_80, c_1954])).
% 10.03/3.87  tff(c_22, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.03/3.87  tff(c_188, plain, (![A_73]: (k4_relat_1(A_73)=k2_funct_1(A_73) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.03/3.87  tff(c_194, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_188])).
% 10.03/3.87  tff(c_200, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_100, c_194])).
% 10.03/3.87  tff(c_6, plain, (![A_6]: (k4_relat_1(k4_relat_1(A_6))=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.03/3.87  tff(c_206, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_200, c_6])).
% 10.03/3.87  tff(c_210, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_206])).
% 10.03/3.87  tff(c_2486, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_2480])).
% 10.03/3.87  tff(c_2495, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_88, c_2486])).
% 10.03/3.87  tff(c_26, plain, (![A_14]: (k5_relat_1(k2_funct_1(A_14), A_14)=k6_relat_1(k2_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.03/3.87  tff(c_104, plain, (![A_14]: (k5_relat_1(k2_funct_1(A_14), A_14)=k6_partfun1(k2_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_26])).
% 10.03/3.87  tff(c_1974, plain, (![B_250, A_251]: (v2_funct_1(B_250) | k2_relat_1(B_250)!=k1_relat_1(A_251) | ~v2_funct_1(k5_relat_1(B_250, A_251)) | ~v1_funct_1(B_250) | ~v1_relat_1(B_250) | ~v1_funct_1(A_251) | ~v1_relat_1(A_251))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.03/3.87  tff(c_1980, plain, (![A_14]: (v2_funct_1(k2_funct_1(A_14)) | k2_relat_1(k2_funct_1(A_14))!=k1_relat_1(A_14) | ~v2_funct_1(k6_partfun1(k2_relat_1(A_14))) | ~v1_funct_1(k2_funct_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_104, c_1974])).
% 10.03/3.87  tff(c_2034, plain, (![A_260]: (v2_funct_1(k2_funct_1(A_260)) | k2_relat_1(k2_funct_1(A_260))!=k1_relat_1(A_260) | ~v1_funct_1(k2_funct_1(A_260)) | ~v1_relat_1(k2_funct_1(A_260)) | ~v2_funct_1(A_260) | ~v1_funct_1(A_260) | ~v1_relat_1(A_260))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1980])).
% 10.03/3.87  tff(c_8, plain, (![A_7]: (k4_relat_1(A_7)=k2_funct_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.03/3.87  tff(c_2518, plain, (![A_332]: (k4_relat_1(k2_funct_1(A_332))=k2_funct_1(k2_funct_1(A_332)) | k2_relat_1(k2_funct_1(A_332))!=k1_relat_1(A_332) | ~v1_funct_1(k2_funct_1(A_332)) | ~v1_relat_1(k2_funct_1(A_332)) | ~v2_funct_1(A_332) | ~v1_funct_1(A_332) | ~v1_relat_1(A_332))), inference(resolution, [status(thm)], [c_2034, c_8])).
% 10.03/3.87  tff(c_2698, plain, (![A_362]: (k4_relat_1(k2_funct_1(A_362))=k2_funct_1(k2_funct_1(A_362)) | k2_relat_1(k2_funct_1(A_362))!=k1_relat_1(A_362) | ~v1_funct_1(k2_funct_1(A_362)) | ~v2_funct_1(A_362) | ~v1_funct_1(A_362) | ~v1_relat_1(A_362))), inference(resolution, [status(thm)], [c_12, c_2518])).
% 10.03/3.87  tff(c_2701, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2495, c_2698])).
% 10.03/3.87  tff(c_2707, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_100, c_84, c_1955, c_210, c_2701])).
% 10.03/3.87  tff(c_2732, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_2707])).
% 10.03/3.87  tff(c_2735, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2732])).
% 10.03/3.87  tff(c_2738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_100, c_84, c_1955, c_2735])).
% 10.03/3.87  tff(c_2740, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_2707])).
% 10.03/3.87  tff(c_1833, plain, (![A_229]: (k2_relat_1(k2_funct_1(A_229))=k1_relat_1(A_229) | ~v2_funct_1(A_229) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.03/3.87  tff(c_56, plain, (![B_33]: (v2_funct_2(B_33, k2_relat_1(B_33)) | ~v5_relat_1(B_33, k2_relat_1(B_33)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_158])).
% 10.03/3.87  tff(c_1839, plain, (![A_229]: (v2_funct_2(k2_funct_1(A_229), k2_relat_1(k2_funct_1(A_229))) | ~v5_relat_1(k2_funct_1(A_229), k1_relat_1(A_229)) | ~v1_relat_1(k2_funct_1(A_229)) | ~v2_funct_1(A_229) | ~v1_funct_1(A_229) | ~v1_relat_1(A_229))), inference(superposition, [status(thm), theory('equality')], [c_1833, c_56])).
% 10.03/3.87  tff(c_2810, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2740, c_1839])).
% 10.03/3.87  tff(c_2825, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_100, c_84, c_1955, c_2810])).
% 10.03/3.87  tff(c_2850, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2825])).
% 10.03/3.87  tff(c_2853, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_2850])).
% 10.03/3.87  tff(c_2857, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_100, c_2853])).
% 10.03/3.87  tff(c_2859, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2825])).
% 10.03/3.87  tff(c_1984, plain, (![A_14]: (v2_funct_1(k2_funct_1(A_14)) | k2_relat_1(k2_funct_1(A_14))!=k1_relat_1(A_14) | ~v1_funct_1(k2_funct_1(A_14)) | ~v1_relat_1(k2_funct_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_1980])).
% 10.03/3.87  tff(c_2739, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_2707])).
% 10.03/3.87  tff(c_2768, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2739, c_22])).
% 10.03/3.87  tff(c_2797, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2495, c_2768])).
% 10.03/3.87  tff(c_3595, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2859, c_2797])).
% 10.03/3.87  tff(c_3596, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3595])).
% 10.03/3.87  tff(c_3599, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1984, c_3596])).
% 10.03/3.87  tff(c_3606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_100, c_84, c_2859, c_2495, c_1955, c_2740, c_3599])).
% 10.03/3.87  tff(c_3607, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_3595])).
% 10.03/3.87  tff(c_2629, plain, (![C_356, B_357, A_358]: (m1_subset_1(k2_funct_1(C_356), k1_zfmisc_1(k2_zfmisc_1(B_357, A_358))) | k2_relset_1(A_358, B_357, C_356)!=B_357 | ~v2_funct_1(C_356) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_358, B_357))) | ~v1_funct_2(C_356, A_358, B_357) | ~v1_funct_1(C_356))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.03/3.87  tff(c_36, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.03/3.87  tff(c_5130, plain, (![B_454, A_455, C_456]: (k1_relset_1(B_454, A_455, k2_funct_1(C_456))=k1_relat_1(k2_funct_1(C_456)) | k2_relset_1(A_455, B_454, C_456)!=B_454 | ~v2_funct_1(C_456) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(A_455, B_454))) | ~v1_funct_2(C_456, A_455, B_454) | ~v1_funct_1(C_456))), inference(resolution, [status(thm)], [c_2629, c_36])).
% 10.03/3.87  tff(c_5166, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_5130])).
% 10.03/3.87  tff(c_5201, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_88, c_3607, c_5166])).
% 10.03/3.87  tff(c_54, plain, (![B_30, A_29, C_31]: (k1_xboole_0=B_30 | k1_relset_1(A_29, B_30, C_31)=A_29 | ~v1_funct_2(C_31, A_29, B_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.03/3.87  tff(c_5579, plain, (![A_463, B_464, C_465]: (k1_xboole_0=A_463 | k1_relset_1(B_464, A_463, k2_funct_1(C_465))=B_464 | ~v1_funct_2(k2_funct_1(C_465), B_464, A_463) | k2_relset_1(A_463, B_464, C_465)!=B_464 | ~v2_funct_1(C_465) | ~m1_subset_1(C_465, k1_zfmisc_1(k2_zfmisc_1(A_463, B_464))) | ~v1_funct_2(C_465, A_463, B_464) | ~v1_funct_1(C_465))), inference(resolution, [status(thm)], [c_2629, c_54])).
% 10.03/3.87  tff(c_5621, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_5579])).
% 10.03/3.87  tff(c_5672, plain, (k1_xboole_0='#skF_1' | k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_88, c_2587, c_5201, c_5621])).
% 10.03/3.87  tff(c_5674, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4002, c_82, c_5672])).
% 10.03/3.87  tff(c_5676, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2498])).
% 10.03/3.87  tff(c_187, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_90, c_175])).
% 10.03/3.87  tff(c_231, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_187, c_222])).
% 10.03/3.87  tff(c_240, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_231])).
% 10.03/3.87  tff(c_242, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_240])).
% 10.03/3.87  tff(c_253, plain, (![A_82, B_83, D_84]: (r2_relset_1(A_82, B_83, D_84, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.03/3.87  tff(c_260, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_101, c_253])).
% 10.03/3.87  tff(c_924, plain, (![E_162, A_159, B_163, D_160, F_161, C_164]: (m1_subset_1(k1_partfun1(A_159, B_163, C_164, D_160, E_162, F_161), k1_zfmisc_1(k2_zfmisc_1(A_159, D_160))) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(C_164, D_160))) | ~v1_funct_1(F_161) | ~m1_subset_1(E_162, k1_zfmisc_1(k2_zfmisc_1(A_159, B_163))) | ~v1_funct_1(E_162))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.03/3.87  tff(c_436, plain, (![D_112, C_113, A_114, B_115]: (D_112=C_113 | ~r2_relset_1(A_114, B_115, C_113, D_112) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.03/3.87  tff(c_444, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_436])).
% 10.03/3.87  tff(c_459, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_444])).
% 10.03/3.87  tff(c_494, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_459])).
% 10.03/3.87  tff(c_943, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_924, c_494])).
% 10.03/3.87  tff(c_994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_943])).
% 10.03/3.87  tff(c_995, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_459])).
% 10.03/3.87  tff(c_1786, plain, (![D_219, A_220, B_221, C_222]: (v2_funct_2(D_219, A_220) | ~r2_relset_1(A_220, A_220, k1_partfun1(A_220, B_221, B_221, A_220, C_222, D_219), k6_partfun1(A_220)) | ~m1_subset_1(D_219, k1_zfmisc_1(k2_zfmisc_1(B_221, A_220))) | ~v1_funct_2(D_219, B_221, A_220) | ~v1_funct_1(D_219) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))) | ~v1_funct_2(C_222, A_220, B_221) | ~v1_funct_1(C_222))), inference(cnfTransformation, [status(thm)], [f_201])).
% 10.03/3.87  tff(c_1792, plain, (v2_funct_2('#skF_4', '#skF_1') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_995, c_1786])).
% 10.03/3.87  tff(c_1797, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_94, c_92, c_90, c_260, c_1792])).
% 10.03/3.87  tff(c_1799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_1797])).
% 10.03/3.87  tff(c_1800, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_240])).
% 10.03/3.87  tff(c_30, plain, (![A_15, B_17]: (k2_funct_1(A_15)=B_17 | k6_relat_1(k2_relat_1(A_15))!=k5_relat_1(B_17, A_15) | k2_relat_1(B_17)!=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.03/3.87  tff(c_5706, plain, (![A_468, B_469]: (k2_funct_1(A_468)=B_469 | k6_partfun1(k2_relat_1(A_468))!=k5_relat_1(B_469, A_468) | k2_relat_1(B_469)!=k1_relat_1(A_468) | ~v2_funct_1(A_468) | ~v1_funct_1(B_469) | ~v1_relat_1(B_469) | ~v1_funct_1(A_468) | ~v1_relat_1(A_468))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_30])).
% 10.03/3.87  tff(c_5714, plain, (![B_469]: (k2_funct_1('#skF_4')=B_469 | k5_relat_1(B_469, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_469)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_469) | ~v1_relat_1(B_469) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1800, c_5706])).
% 10.03/3.87  tff(c_5719, plain, (![B_470]: (k2_funct_1('#skF_4')=B_470 | k5_relat_1(B_470, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_470)!='#skF_2' | ~v1_funct_1(B_470) | ~v1_relat_1(B_470))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_94, c_5676, c_1959, c_5714])).
% 10.03/3.87  tff(c_5725, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_158, c_5719])).
% 10.03/3.87  tff(c_5740, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5725])).
% 10.03/3.87  tff(c_5759, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_5740])).
% 10.03/3.87  tff(c_5795, plain, (![C_484, B_485, A_486]: (v1_funct_2(k2_funct_1(C_484), B_485, A_486) | k2_relset_1(A_486, B_485, C_484)!=B_485 | ~v2_funct_1(C_484) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_486, B_485))) | ~v1_funct_2(C_484, A_486, B_485) | ~v1_funct_1(C_484))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.03/3.87  tff(c_5801, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_5795])).
% 10.03/3.87  tff(c_5810, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_88, c_5801])).
% 10.03/3.87  tff(c_5913, plain, (![C_502, B_503, A_504]: (m1_subset_1(k2_funct_1(C_502), k1_zfmisc_1(k2_zfmisc_1(B_503, A_504))) | k2_relset_1(A_504, B_503, C_502)!=B_503 | ~v2_funct_1(C_502) | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_504, B_503))) | ~v1_funct_2(C_502, A_504, B_503) | ~v1_funct_1(C_502))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.03/3.87  tff(c_7628, plain, (![B_562, A_563, C_564]: (k1_relset_1(B_562, A_563, k2_funct_1(C_564))=k1_relat_1(k2_funct_1(C_564)) | k2_relset_1(A_563, B_562, C_564)!=B_562 | ~v2_funct_1(C_564) | ~m1_subset_1(C_564, k1_zfmisc_1(k2_zfmisc_1(A_563, B_562))) | ~v1_funct_2(C_564, A_563, B_562) | ~v1_funct_1(C_564))), inference(resolution, [status(thm)], [c_5913, c_36])).
% 10.03/3.87  tff(c_7667, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_7628])).
% 10.03/3.87  tff(c_7705, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_88, c_7667])).
% 10.03/3.87  tff(c_8077, plain, (![A_570, B_571, C_572]: (k1_xboole_0=A_570 | k1_relset_1(B_571, A_570, k2_funct_1(C_572))=B_571 | ~v1_funct_2(k2_funct_1(C_572), B_571, A_570) | k2_relset_1(A_570, B_571, C_572)!=B_571 | ~v2_funct_1(C_572) | ~m1_subset_1(C_572, k1_zfmisc_1(k2_zfmisc_1(A_570, B_571))) | ~v1_funct_2(C_572, A_570, B_571) | ~v1_funct_1(C_572))), inference(resolution, [status(thm)], [c_5913, c_54])).
% 10.03/3.87  tff(c_8122, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_8077])).
% 10.03/3.87  tff(c_8177, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_88, c_5810, c_7705, c_8122])).
% 10.03/3.87  tff(c_8178, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_8177])).
% 10.03/3.87  tff(c_24, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.03/3.87  tff(c_8187, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8178, c_24])).
% 10.03/3.87  tff(c_8194, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_100, c_84, c_8187])).
% 10.03/3.87  tff(c_8196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5759, c_8194])).
% 10.03/3.87  tff(c_8198, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_5740])).
% 10.03/3.87  tff(c_8204, plain, (v2_funct_2('#skF_3', k2_relat_1('#skF_3')) | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8198, c_56])).
% 10.03/3.87  tff(c_8210, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_186, c_8198, c_8204])).
% 10.03/3.87  tff(c_8212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_8210])).
% 10.03/3.87  tff(c_8213, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_237])).
% 10.03/3.87  tff(c_11265, plain, (![C_924, A_925, B_926]: (v1_funct_1(k2_funct_1(C_924)) | k2_relset_1(A_925, B_926, C_924)!=B_926 | ~v2_funct_1(C_924) | ~m1_subset_1(C_924, k1_zfmisc_1(k2_zfmisc_1(A_925, B_926))) | ~v1_funct_2(C_924, A_925, B_926) | ~v1_funct_1(C_924))), inference(cnfTransformation, [status(thm)], [f_217])).
% 10.03/3.87  tff(c_11274, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_11265])).
% 10.03/3.87  tff(c_11283, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_11274])).
% 10.03/3.87  tff(c_11284, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_11283])).
% 10.03/3.87  tff(c_11066, plain, (![A_892, B_893, C_894]: (k1_relset_1(A_892, B_893, C_894)=k1_relat_1(C_894) | ~m1_subset_1(C_894, k1_zfmisc_1(k2_zfmisc_1(A_892, B_893))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.03/3.87  tff(c_11078, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_11066])).
% 10.03/3.87  tff(c_11138, plain, (![B_905, A_906, C_907]: (k1_xboole_0=B_905 | k1_relset_1(A_906, B_905, C_907)=A_906 | ~v1_funct_2(C_907, A_906, B_905) | ~m1_subset_1(C_907, k1_zfmisc_1(k2_zfmisc_1(A_906, B_905))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 10.03/3.87  tff(c_11147, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_90, c_11138])).
% 10.03/3.87  tff(c_11156, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_11078, c_11147])).
% 10.03/3.87  tff(c_11157, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_82, c_11156])).
% 10.03/3.87  tff(c_11423, plain, (![C_963, B_964, E_959, D_961, A_960, F_962]: (k1_partfun1(A_960, B_964, C_963, D_961, E_959, F_962)=k5_relat_1(E_959, F_962) | ~m1_subset_1(F_962, k1_zfmisc_1(k2_zfmisc_1(C_963, D_961))) | ~v1_funct_1(F_962) | ~m1_subset_1(E_959, k1_zfmisc_1(k2_zfmisc_1(A_960, B_964))) | ~v1_funct_1(E_959))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.03/3.87  tff(c_11429, plain, (![A_960, B_964, E_959]: (k1_partfun1(A_960, B_964, '#skF_2', '#skF_1', E_959, '#skF_4')=k5_relat_1(E_959, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_959, k1_zfmisc_1(k2_zfmisc_1(A_960, B_964))) | ~v1_funct_1(E_959))), inference(resolution, [status(thm)], [c_90, c_11423])).
% 10.03/3.87  tff(c_11465, plain, (![A_969, B_970, E_971]: (k1_partfun1(A_969, B_970, '#skF_2', '#skF_1', E_971, '#skF_4')=k5_relat_1(E_971, '#skF_4') | ~m1_subset_1(E_971, k1_zfmisc_1(k2_zfmisc_1(A_969, B_970))) | ~v1_funct_1(E_971))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_11429])).
% 10.03/3.87  tff(c_11471, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_11465])).
% 10.03/3.87  tff(c_11478, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_11471])).
% 10.03/3.87  tff(c_11227, plain, (![D_917, C_918, A_919, B_920]: (D_917=C_918 | ~r2_relset_1(A_919, B_920, C_918, D_917) | ~m1_subset_1(D_917, k1_zfmisc_1(k2_zfmisc_1(A_919, B_920))) | ~m1_subset_1(C_918, k1_zfmisc_1(k2_zfmisc_1(A_919, B_920))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.03/3.87  tff(c_11235, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_11227])).
% 10.03/3.87  tff(c_11250, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_11235])).
% 10.03/3.87  tff(c_11285, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_11250])).
% 10.03/3.87  tff(c_11483, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11478, c_11285])).
% 10.03/3.87  tff(c_11599, plain, (![C_985, A_980, E_983, D_981, B_984, F_982]: (m1_subset_1(k1_partfun1(A_980, B_984, C_985, D_981, E_983, F_982), k1_zfmisc_1(k2_zfmisc_1(A_980, D_981))) | ~m1_subset_1(F_982, k1_zfmisc_1(k2_zfmisc_1(C_985, D_981))) | ~v1_funct_1(F_982) | ~m1_subset_1(E_983, k1_zfmisc_1(k2_zfmisc_1(A_980, B_984))) | ~v1_funct_1(E_983))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.03/3.87  tff(c_11661, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11478, c_11599])).
% 10.03/3.87  tff(c_11692, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_11661])).
% 10.03/3.87  tff(c_11694, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11483, c_11692])).
% 10.03/3.87  tff(c_11695, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_11250])).
% 10.03/3.87  tff(c_12012, plain, (![C_1036, B_1037, D_1034, E_1032, A_1033, F_1035]: (k1_partfun1(A_1033, B_1037, C_1036, D_1034, E_1032, F_1035)=k5_relat_1(E_1032, F_1035) | ~m1_subset_1(F_1035, k1_zfmisc_1(k2_zfmisc_1(C_1036, D_1034))) | ~v1_funct_1(F_1035) | ~m1_subset_1(E_1032, k1_zfmisc_1(k2_zfmisc_1(A_1033, B_1037))) | ~v1_funct_1(E_1032))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.03/3.87  tff(c_12020, plain, (![A_1033, B_1037, E_1032]: (k1_partfun1(A_1033, B_1037, '#skF_2', '#skF_1', E_1032, '#skF_4')=k5_relat_1(E_1032, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1032, k1_zfmisc_1(k2_zfmisc_1(A_1033, B_1037))) | ~v1_funct_1(E_1032))), inference(resolution, [status(thm)], [c_90, c_12012])).
% 10.03/3.87  tff(c_12073, plain, (![A_1042, B_1043, E_1044]: (k1_partfun1(A_1042, B_1043, '#skF_2', '#skF_1', E_1044, '#skF_4')=k5_relat_1(E_1044, '#skF_4') | ~m1_subset_1(E_1044, k1_zfmisc_1(k2_zfmisc_1(A_1042, B_1043))) | ~v1_funct_1(E_1044))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_12020])).
% 10.03/3.87  tff(c_12082, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_12073])).
% 10.03/3.87  tff(c_12090, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_11695, c_12082])).
% 10.03/3.87  tff(c_12203, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12090, c_18])).
% 10.03/3.87  tff(c_12210, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_94, c_158, c_100, c_105, c_8213, c_11157, c_12203])).
% 10.03/3.87  tff(c_12212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11284, c_12210])).
% 10.03/3.87  tff(c_12214, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_11283])).
% 10.03/3.87  tff(c_8224, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_240])).
% 10.03/3.87  tff(c_8248, plain, (![A_576, B_577, D_578]: (r2_relset_1(A_576, B_577, D_578, D_578) | ~m1_subset_1(D_578, k1_zfmisc_1(k2_zfmisc_1(A_576, B_577))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.03/3.87  tff(c_8255, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_101, c_8248])).
% 10.03/3.87  tff(c_9870, plain, (![A_791, E_790, B_795, C_794, F_793, D_792]: (k1_partfun1(A_791, B_795, C_794, D_792, E_790, F_793)=k5_relat_1(E_790, F_793) | ~m1_subset_1(F_793, k1_zfmisc_1(k2_zfmisc_1(C_794, D_792))) | ~v1_funct_1(F_793) | ~m1_subset_1(E_790, k1_zfmisc_1(k2_zfmisc_1(A_791, B_795))) | ~v1_funct_1(E_790))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.03/3.87  tff(c_9878, plain, (![A_791, B_795, E_790]: (k1_partfun1(A_791, B_795, '#skF_2', '#skF_1', E_790, '#skF_4')=k5_relat_1(E_790, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_790, k1_zfmisc_1(k2_zfmisc_1(A_791, B_795))) | ~v1_funct_1(E_790))), inference(resolution, [status(thm)], [c_90, c_9870])).
% 10.03/3.87  tff(c_9951, plain, (![A_796, B_797, E_798]: (k1_partfun1(A_796, B_797, '#skF_2', '#skF_1', E_798, '#skF_4')=k5_relat_1(E_798, '#skF_4') | ~m1_subset_1(E_798, k1_zfmisc_1(k2_zfmisc_1(A_796, B_797))) | ~v1_funct_1(E_798))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_9878])).
% 10.03/3.87  tff(c_9960, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_9951])).
% 10.03/3.87  tff(c_9968, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_9960])).
% 10.03/3.87  tff(c_8419, plain, (![D_605, C_606, A_607, B_608]: (D_605=C_606 | ~r2_relset_1(A_607, B_608, C_606, D_605) | ~m1_subset_1(D_605, k1_zfmisc_1(k2_zfmisc_1(A_607, B_608))) | ~m1_subset_1(C_606, k1_zfmisc_1(k2_zfmisc_1(A_607, B_608))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.03/3.87  tff(c_8427, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_86, c_8419])).
% 10.03/3.87  tff(c_8442, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_8427])).
% 10.03/3.87  tff(c_9388, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_8442])).
% 10.03/3.87  tff(c_9973, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9968, c_9388])).
% 10.03/3.87  tff(c_9989, plain, (![F_801, E_802, D_800, A_799, B_803, C_804]: (m1_subset_1(k1_partfun1(A_799, B_803, C_804, D_800, E_802, F_801), k1_zfmisc_1(k2_zfmisc_1(A_799, D_800))) | ~m1_subset_1(F_801, k1_zfmisc_1(k2_zfmisc_1(C_804, D_800))) | ~v1_funct_1(F_801) | ~m1_subset_1(E_802, k1_zfmisc_1(k2_zfmisc_1(A_799, B_803))) | ~v1_funct_1(E_802))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.03/3.87  tff(c_10051, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9968, c_9989])).
% 10.03/3.87  tff(c_10076, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_10051])).
% 10.03/3.87  tff(c_10078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9973, c_10076])).
% 10.03/3.87  tff(c_10079, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_8442])).
% 10.03/3.87  tff(c_11007, plain, (![D_881, A_882, B_883, C_884]: (v2_funct_2(D_881, A_882) | ~r2_relset_1(A_882, A_882, k1_partfun1(A_882, B_883, B_883, A_882, C_884, D_881), k6_partfun1(A_882)) | ~m1_subset_1(D_881, k1_zfmisc_1(k2_zfmisc_1(B_883, A_882))) | ~v1_funct_2(D_881, B_883, A_882) | ~v1_funct_1(D_881) | ~m1_subset_1(C_884, k1_zfmisc_1(k2_zfmisc_1(A_882, B_883))) | ~v1_funct_2(C_884, A_882, B_883) | ~v1_funct_1(C_884))), inference(cnfTransformation, [status(thm)], [f_201])).
% 10.03/3.87  tff(c_11013, plain, (v2_funct_2('#skF_4', '#skF_1') | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10079, c_11007])).
% 10.03/3.87  tff(c_11017, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_96, c_94, c_92, c_90, c_8255, c_11013])).
% 10.03/3.87  tff(c_11019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8224, c_11017])).
% 10.03/3.87  tff(c_11020, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_240])).
% 10.03/3.87  tff(c_12784, plain, (![A_1122, B_1123]: (k2_funct_1(A_1122)=B_1123 | k6_partfun1(k2_relat_1(A_1122))!=k5_relat_1(B_1123, A_1122) | k2_relat_1(B_1123)!=k1_relat_1(A_1122) | ~v2_funct_1(A_1122) | ~v1_funct_1(B_1123) | ~v1_relat_1(B_1123) | ~v1_funct_1(A_1122) | ~v1_relat_1(A_1122))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_30])).
% 10.03/3.87  tff(c_12792, plain, (![B_1123]: (k2_funct_1('#skF_4')=B_1123 | k5_relat_1(B_1123, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1123)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_1123) | ~v1_relat_1(B_1123) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11020, c_12784])).
% 10.03/3.87  tff(c_12801, plain, (![B_1124]: (k2_funct_1('#skF_4')=B_1124 | k5_relat_1(B_1124, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_1124)!='#skF_2' | ~v1_funct_1(B_1124) | ~v1_relat_1(B_1124))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_94, c_12214, c_11157, c_12792])).
% 10.03/3.87  tff(c_12807, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_158, c_12801])).
% 10.03/3.87  tff(c_12822, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_8213, c_12807])).
% 10.03/3.87  tff(c_12826, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_12822])).
% 10.03/3.87  tff(c_12577, plain, (![B_1107, D_1104, E_1102, A_1103, C_1106, F_1105]: (k1_partfun1(A_1103, B_1107, C_1106, D_1104, E_1102, F_1105)=k5_relat_1(E_1102, F_1105) | ~m1_subset_1(F_1105, k1_zfmisc_1(k2_zfmisc_1(C_1106, D_1104))) | ~v1_funct_1(F_1105) | ~m1_subset_1(E_1102, k1_zfmisc_1(k2_zfmisc_1(A_1103, B_1107))) | ~v1_funct_1(E_1102))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.03/3.87  tff(c_12585, plain, (![A_1103, B_1107, E_1102]: (k1_partfun1(A_1103, B_1107, '#skF_2', '#skF_1', E_1102, '#skF_4')=k5_relat_1(E_1102, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1102, k1_zfmisc_1(k2_zfmisc_1(A_1103, B_1107))) | ~v1_funct_1(E_1102))), inference(resolution, [status(thm)], [c_90, c_12577])).
% 10.03/3.87  tff(c_12626, plain, (![A_1112, B_1113, E_1114]: (k1_partfun1(A_1112, B_1113, '#skF_2', '#skF_1', E_1114, '#skF_4')=k5_relat_1(E_1114, '#skF_4') | ~m1_subset_1(E_1114, k1_zfmisc_1(k2_zfmisc_1(A_1112, B_1113))) | ~v1_funct_1(E_1114))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_12585])).
% 10.03/3.87  tff(c_12635, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_12626])).
% 10.03/3.87  tff(c_12643, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_12635])).
% 10.03/3.87  tff(c_12230, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_11250])).
% 10.03/3.87  tff(c_12648, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12643, c_12230])).
% 10.03/3.87  tff(c_12654, plain, (![C_1120, D_1116, A_1115, E_1118, F_1117, B_1119]: (m1_subset_1(k1_partfun1(A_1115, B_1119, C_1120, D_1116, E_1118, F_1117), k1_zfmisc_1(k2_zfmisc_1(A_1115, D_1116))) | ~m1_subset_1(F_1117, k1_zfmisc_1(k2_zfmisc_1(C_1120, D_1116))) | ~v1_funct_1(F_1117) | ~m1_subset_1(E_1118, k1_zfmisc_1(k2_zfmisc_1(A_1115, B_1119))) | ~v1_funct_1(E_1118))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.03/3.87  tff(c_12719, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12643, c_12654])).
% 10.03/3.87  tff(c_12750, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_96, c_94, c_90, c_12719])).
% 10.03/3.87  tff(c_12761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12648, c_12750])).
% 10.03/3.87  tff(c_12762, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_11250])).
% 10.03/3.87  tff(c_12982, plain, (![C_1156, B_1157, D_1154, E_1152, F_1155, A_1153]: (k1_partfun1(A_1153, B_1157, C_1156, D_1154, E_1152, F_1155)=k5_relat_1(E_1152, F_1155) | ~m1_subset_1(F_1155, k1_zfmisc_1(k2_zfmisc_1(C_1156, D_1154))) | ~v1_funct_1(F_1155) | ~m1_subset_1(E_1152, k1_zfmisc_1(k2_zfmisc_1(A_1153, B_1157))) | ~v1_funct_1(E_1152))), inference(cnfTransformation, [status(thm)], [f_180])).
% 10.03/3.87  tff(c_12988, plain, (![A_1153, B_1157, E_1152]: (k1_partfun1(A_1153, B_1157, '#skF_2', '#skF_1', E_1152, '#skF_4')=k5_relat_1(E_1152, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1152, k1_zfmisc_1(k2_zfmisc_1(A_1153, B_1157))) | ~v1_funct_1(E_1152))), inference(resolution, [status(thm)], [c_90, c_12982])).
% 10.03/3.87  tff(c_13110, plain, (![A_1166, B_1167, E_1168]: (k1_partfun1(A_1166, B_1167, '#skF_2', '#skF_1', E_1168, '#skF_4')=k5_relat_1(E_1168, '#skF_4') | ~m1_subset_1(E_1168, k1_zfmisc_1(k2_zfmisc_1(A_1166, B_1167))) | ~v1_funct_1(E_1168))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_12988])).
% 10.03/3.87  tff(c_13119, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_13110])).
% 10.03/3.87  tff(c_13127, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_12762, c_13119])).
% 10.03/3.87  tff(c_13129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12826, c_13127])).
% 10.03/3.87  tff(c_13130, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_12822])).
% 10.03/3.87  tff(c_12217, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12214, c_8])).
% 10.03/3.87  tff(c_12220, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_94, c_12217])).
% 10.03/3.87  tff(c_12224, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12220, c_6])).
% 10.03/3.87  tff(c_12228, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_12224])).
% 10.03/3.87  tff(c_13133, plain, (k4_relat_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13130, c_12228])).
% 10.03/3.87  tff(c_13189, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13133, c_200])).
% 10.03/3.87  tff(c_13191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_13189])).
% 10.03/3.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.03/3.87  
% 10.03/3.87  Inference rules
% 10.03/3.87  ----------------------
% 10.03/3.87  #Ref     : 0
% 10.03/3.87  #Sup     : 2702
% 10.03/3.87  #Fact    : 0
% 10.03/3.87  #Define  : 0
% 10.03/3.87  #Split   : 99
% 10.03/3.87  #Chain   : 0
% 10.03/3.87  #Close   : 0
% 10.03/3.87  
% 10.03/3.87  Ordering : KBO
% 10.03/3.87  
% 10.03/3.87  Simplification rules
% 10.03/3.87  ----------------------
% 10.03/3.87  #Subsume      : 164
% 10.03/3.87  #Demod        : 2644
% 10.03/3.87  #Tautology    : 573
% 10.03/3.87  #SimpNegUnit  : 158
% 10.03/3.87  #BackRed      : 84
% 10.03/3.87  
% 10.03/3.87  #Partial instantiations: 0
% 10.03/3.87  #Strategies tried      : 1
% 10.03/3.87  
% 10.03/3.87  Timing (in seconds)
% 10.03/3.87  ----------------------
% 10.03/3.88  Preprocessing        : 0.37
% 10.03/3.88  Parsing              : 0.19
% 10.03/3.88  CNF conversion       : 0.03
% 10.03/3.88  Main loop            : 2.68
% 10.03/3.88  Inferencing          : 0.87
% 10.03/3.88  Reduction            : 1.04
% 10.03/3.88  Demodulation         : 0.77
% 10.03/3.88  BG Simplification    : 0.08
% 10.03/3.88  Subsumption          : 0.49
% 10.03/3.88  Abstraction          : 0.10
% 10.03/3.88  MUC search           : 0.00
% 10.03/3.88  Cooper               : 0.00
% 10.03/3.88  Total                : 3.15
% 10.03/3.88  Index Insertion      : 0.00
% 10.03/3.88  Index Deletion       : 0.00
% 10.03/3.88  Index Matching       : 0.00
% 10.03/3.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
