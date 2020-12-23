%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:17 EST 2020

% Result     : Theorem 15.87s
% Output     : CNFRefutation 15.87s
% Verified   : 
% Statistics : Number of formulae       :  216 (4244 expanded)
%              Number of leaves         :   53 (1531 expanded)
%              Depth                    :   22
%              Number of atoms          :  522 (15303 expanded)
%              Number of equality atoms :  175 (4152 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_271,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_229,axiom,(
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

tff(f_213,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_159,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_185,axiom,(
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

tff(f_211,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_201,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_167,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_197,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_108,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_245,axiom,(
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

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_155,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(c_94,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_218,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_227,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_106,c_218])).

tff(c_236,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_227])).

tff(c_110,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_22,plain,(
    ! [A_15] :
      ( v1_funct_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_26440,plain,(
    ! [C_724,A_725,B_726] :
      ( v1_funct_1(k2_funct_1(C_724))
      | k2_relset_1(A_725,B_726,C_724) != B_726
      | ~ v2_funct_1(C_724)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(k2_zfmisc_1(A_725,B_726)))
      | ~ v1_funct_2(C_724,A_725,B_726)
      | ~ v1_funct_1(C_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_26449,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_26440])).

tff(c_26458,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_26449])).

tff(c_26459,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26458])).

tff(c_112,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_224,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_112,c_218])).

tff(c_233,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_224])).

tff(c_116,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_82,plain,(
    ! [A_50] : k6_relat_1(A_50) = k6_partfun1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_28,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_28])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_325,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_338,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_106,c_325])).

tff(c_20523,plain,(
    ! [B_634,A_635,C_636] :
      ( k1_xboole_0 = B_634
      | k1_relset_1(A_635,B_634,C_636) = A_635
      | ~ v1_funct_2(C_636,A_635,B_634)
      | ~ m1_subset_1(C_636,k1_zfmisc_1(k2_zfmisc_1(A_635,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_20532,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_106,c_20523])).

tff(c_20541,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_338,c_20532])).

tff(c_20542,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_20541])).

tff(c_24810,plain,(
    ! [C_699,B_700,A_701,D_698,E_696,F_697] :
      ( k1_partfun1(A_701,B_700,C_699,D_698,E_696,F_697) = k5_relat_1(E_696,F_697)
      | ~ m1_subset_1(F_697,k1_zfmisc_1(k2_zfmisc_1(C_699,D_698)))
      | ~ v1_funct_1(F_697)
      | ~ m1_subset_1(E_696,k1_zfmisc_1(k2_zfmisc_1(A_701,B_700)))
      | ~ v1_funct_1(E_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_24816,plain,(
    ! [A_701,B_700,E_696] :
      ( k1_partfun1(A_701,B_700,'#skF_2','#skF_1',E_696,'#skF_4') = k5_relat_1(E_696,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_696,k1_zfmisc_1(k2_zfmisc_1(A_701,B_700)))
      | ~ v1_funct_1(E_696) ) ),
    inference(resolution,[status(thm)],[c_106,c_24810])).

tff(c_24825,plain,(
    ! [A_702,B_703,E_704] :
      ( k1_partfun1(A_702,B_703,'#skF_2','#skF_1',E_704,'#skF_4') = k5_relat_1(E_704,'#skF_4')
      | ~ m1_subset_1(E_704,k1_zfmisc_1(k2_zfmisc_1(A_702,B_703)))
      | ~ v1_funct_1(E_704) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_24816])).

tff(c_24831,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_24825])).

tff(c_24838,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_24831])).

tff(c_78,plain,(
    ! [A_43] : m1_subset_1(k6_partfun1(A_43),k1_zfmisc_1(k2_zfmisc_1(A_43,A_43))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_102,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_21493,plain,(
    ! [D_648,C_649,A_650,B_651] :
      ( D_648 = C_649
      | ~ r2_relset_1(A_650,B_651,C_649,D_648)
      | ~ m1_subset_1(D_648,k1_zfmisc_1(k2_zfmisc_1(A_650,B_651)))
      | ~ m1_subset_1(C_649,k1_zfmisc_1(k2_zfmisc_1(A_650,B_651))) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_21501,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_102,c_21493])).

tff(c_21516,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_21501])).

tff(c_21868,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_21516])).

tff(c_25789,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24838,c_21868])).

tff(c_26088,plain,(
    ! [D_717,E_718,F_716,C_719,B_715,A_714] :
      ( m1_subset_1(k1_partfun1(A_714,B_715,C_719,D_717,E_718,F_716),k1_zfmisc_1(k2_zfmisc_1(A_714,D_717)))
      | ~ m1_subset_1(F_716,k1_zfmisc_1(k2_zfmisc_1(C_719,D_717)))
      | ~ v1_funct_1(F_716)
      | ~ m1_subset_1(E_718,k1_zfmisc_1(k2_zfmisc_1(A_714,B_715)))
      | ~ v1_funct_1(E_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_26140,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24838,c_26088])).

tff(c_26164,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_112,c_110,c_106,c_26140])).

tff(c_26166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25789,c_26164])).

tff(c_26167,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_21516])).

tff(c_30309,plain,(
    ! [A_779,B_778,E_774,F_775,D_776,C_777] :
      ( k1_partfun1(A_779,B_778,C_777,D_776,E_774,F_775) = k5_relat_1(E_774,F_775)
      | ~ m1_subset_1(F_775,k1_zfmisc_1(k2_zfmisc_1(C_777,D_776)))
      | ~ v1_funct_1(F_775)
      | ~ m1_subset_1(E_774,k1_zfmisc_1(k2_zfmisc_1(A_779,B_778)))
      | ~ v1_funct_1(E_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_30315,plain,(
    ! [A_779,B_778,E_774] :
      ( k1_partfun1(A_779,B_778,'#skF_2','#skF_1',E_774,'#skF_4') = k5_relat_1(E_774,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_774,k1_zfmisc_1(k2_zfmisc_1(A_779,B_778)))
      | ~ v1_funct_1(E_774) ) ),
    inference(resolution,[status(thm)],[c_106,c_30309])).

tff(c_34301,plain,(
    ! [A_840,B_841,E_842] :
      ( k1_partfun1(A_840,B_841,'#skF_2','#skF_1',E_842,'#skF_4') = k5_relat_1(E_842,'#skF_4')
      | ~ m1_subset_1(E_842,k1_zfmisc_1(k2_zfmisc_1(A_840,B_841)))
      | ~ v1_funct_1(E_842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_30315])).

tff(c_34310,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_34301])).

tff(c_34318,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_26167,c_34310])).

tff(c_36,plain,(
    ! [A_18,B_20] :
      ( v2_funct_1(A_18)
      | k2_relat_1(B_20) != k1_relat_1(A_18)
      | ~ v2_funct_1(k5_relat_1(B_20,A_18))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34339,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34318,c_36])).

tff(c_34350,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_110,c_233,c_116,c_120,c_20542,c_34339])).

tff(c_34351,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_26459,c_34350])).

tff(c_14,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,(
    ! [A_11] : k2_relat_1(k6_partfun1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_14])).

tff(c_96,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_114,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_104,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_100,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_16,plain,(
    ! [A_12] : k4_relat_1(k6_relat_1(A_12)) = k6_relat_1(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [A_12] : k4_relat_1(k6_partfun1(A_12)) = k6_partfun1(A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_16])).

tff(c_48,plain,(
    ! [A_23] :
      ( k5_relat_1(k2_funct_1(A_23),A_23) = k6_relat_1(k2_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_536,plain,(
    ! [A_96] :
      ( k5_relat_1(k2_funct_1(A_96),A_96) = k6_partfun1(k2_relat_1(A_96))
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_48])).

tff(c_247,plain,(
    ! [A_77] :
      ( k4_relat_1(A_77) = k2_funct_1(A_77)
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_256,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_247])).

tff(c_263,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_116,c_256])).

tff(c_4,plain,(
    ! [A_4] :
      ( v1_relat_1(k4_relat_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_270,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_4])).

tff(c_276,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_270])).

tff(c_8,plain,(
    ! [A_7] :
      ( k4_relat_1(k4_relat_1(A_7)) = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_267,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_8])).

tff(c_274,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_267])).

tff(c_357,plain,(
    ! [B_90,A_91] :
      ( k5_relat_1(k4_relat_1(B_90),k4_relat_1(A_91)) = k4_relat_1(k5_relat_1(A_91,B_90))
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_372,plain,(
    ! [A_91] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_91)) = k4_relat_1(k5_relat_1(A_91,'#skF_3'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_357])).

tff(c_402,plain,(
    ! [A_92] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_92)) = k4_relat_1(k5_relat_1(A_92,'#skF_3'))
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_372])).

tff(c_411,plain,
    ( k4_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_402])).

tff(c_424,plain,(
    k4_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_411])).

tff(c_542,plain,
    ( k4_relat_1(k6_partfun1(k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_424])).

tff(c_548,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_116,c_100,c_123,c_542])).

tff(c_34402,plain,(
    ! [B_843,C_844,A_845] :
      ( k6_partfun1(B_843) = k5_relat_1(k2_funct_1(C_844),C_844)
      | k1_xboole_0 = B_843
      | ~ v2_funct_1(C_844)
      | k2_relset_1(A_845,B_843,C_844) != B_843
      | ~ m1_subset_1(C_844,k1_zfmisc_1(k2_zfmisc_1(A_845,B_843)))
      | ~ v1_funct_2(C_844,A_845,B_843)
      | ~ v1_funct_1(C_844) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_34408,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_34402])).

tff(c_34417,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_104,c_100,c_548,c_34408])).

tff(c_34418,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_34417])).

tff(c_34528,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34418,c_124])).

tff(c_34573,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_34528])).

tff(c_34575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34351,c_34573])).

tff(c_34577,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26458])).

tff(c_20,plain,(
    ! [A_14] :
      ( k4_relat_1(A_14) = k2_funct_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34580,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34577,c_20])).

tff(c_34583,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_110,c_34580])).

tff(c_34643,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34583,c_4])).

tff(c_34685,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_34643])).

tff(c_119,plain,(
    ! [A_23] :
      ( k5_relat_1(k2_funct_1(A_23),A_23) = k6_partfun1(k2_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_48])).

tff(c_43449,plain,(
    ! [A_1025,B_1026] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_1025),B_1026)) = k5_relat_1(k4_relat_1(B_1026),A_1025)
      | ~ v1_relat_1(B_1026)
      | ~ v1_relat_1(k4_relat_1(A_1025))
      | ~ v1_relat_1(A_1025) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_357])).

tff(c_43574,plain,(
    ! [B_1026] :
      ( k4_relat_1(k5_relat_1(k2_funct_1('#skF_4'),B_1026)) = k5_relat_1(k4_relat_1(B_1026),'#skF_4')
      | ~ v1_relat_1(B_1026)
      | ~ v1_relat_1(k4_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34583,c_43449])).

tff(c_44180,plain,(
    ! [B_1030] :
      ( k4_relat_1(k5_relat_1(k2_funct_1('#skF_4'),B_1030)) = k5_relat_1(k4_relat_1(B_1030),'#skF_4')
      | ~ v1_relat_1(B_1030) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_34685,c_34583,c_43574])).

tff(c_44303,plain,
    ( k4_relat_1(k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k4_relat_1('#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_44180])).

tff(c_44334,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1(k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_110,c_34577,c_236,c_123,c_34583,c_44303])).

tff(c_38,plain,(
    ! [B_20,A_18] :
      ( v2_funct_1(B_20)
      | k2_relat_1(B_20) != k1_relat_1(A_18)
      | ~ v2_funct_1(k5_relat_1(B_20,A_18))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44356,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1(k2_relat_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_44334,c_38])).

tff(c_44374,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_110,c_34685,c_120,c_20542,c_44356])).

tff(c_44382,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44374])).

tff(c_44385,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_44382])).

tff(c_44389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_110,c_44385])).

tff(c_44391,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44374])).

tff(c_40,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44390,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2'
    | v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44374])).

tff(c_44394,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44390])).

tff(c_44397,plain,
    ( k1_relat_1('#skF_4') != '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_44394])).

tff(c_44400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_110,c_34577,c_20542,c_44397])).

tff(c_44402,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44390])).

tff(c_42773,plain,(
    ! [B_1013,C_1014,A_1015] :
      ( k6_partfun1(B_1013) = k5_relat_1(k2_funct_1(C_1014),C_1014)
      | k1_xboole_0 = B_1013
      | ~ v2_funct_1(C_1014)
      | k2_relset_1(A_1015,B_1013,C_1014) != B_1013
      | ~ m1_subset_1(C_1014,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1013)))
      | ~ v1_funct_2(C_1014,A_1015,B_1013)
      | ~ v1_funct_1(C_1014) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_42779,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_42773])).

tff(c_42788,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_114,c_104,c_100,c_548,c_42779])).

tff(c_42789,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_42788])).

tff(c_42902,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42789,c_124])).

tff(c_42948,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_42902])).

tff(c_337,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_325])).

tff(c_20529,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_20523])).

tff(c_20537,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_337,c_20529])).

tff(c_20538,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_20537])).

tff(c_20813,plain,(
    ! [B_639,A_640] :
      ( v2_funct_1(B_639)
      | k2_relat_1(B_639) != k1_relat_1(A_640)
      | ~ v2_funct_1(k5_relat_1(B_639,A_640))
      | ~ v1_funct_1(B_639)
      | ~ v1_relat_1(B_639)
      | ~ v1_funct_1(A_640)
      | ~ v1_relat_1(A_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_20855,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1(k2_relat_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_20813])).

tff(c_20910,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1'
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_116,c_276,c_120,c_20538,c_20855])).

tff(c_20927,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_20910])).

tff(c_20930,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_20927])).

tff(c_20934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_116,c_20930])).

tff(c_20936,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20910])).

tff(c_20935,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1'
    | v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20910])).

tff(c_20939,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_20935])).

tff(c_20942,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_20939])).

tff(c_20945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_116,c_100,c_20538,c_20942])).

tff(c_20946,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20935])).

tff(c_20950,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20946,c_20])).

tff(c_20953,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_20936,c_274,c_20950])).

tff(c_44,plain,(
    ! [A_22] :
      ( k2_relat_1(k5_relat_1(A_22,k2_funct_1(A_22))) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_20971,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20953,c_44])).

tff(c_20999,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_20936,c_20946,c_124,c_548,c_20971])).

tff(c_20947,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20935])).

tff(c_42310,plain,(
    ! [B_1000,D_998,E_996,C_999,A_1001,F_997] :
      ( k1_partfun1(A_1001,B_1000,C_999,D_998,E_996,F_997) = k5_relat_1(E_996,F_997)
      | ~ m1_subset_1(F_997,k1_zfmisc_1(k2_zfmisc_1(C_999,D_998)))
      | ~ v1_funct_1(F_997)
      | ~ m1_subset_1(E_996,k1_zfmisc_1(k2_zfmisc_1(A_1001,B_1000)))
      | ~ v1_funct_1(E_996) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_42316,plain,(
    ! [A_1001,B_1000,E_996] :
      ( k1_partfun1(A_1001,B_1000,'#skF_2','#skF_1',E_996,'#skF_4') = k5_relat_1(E_996,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_996,k1_zfmisc_1(k2_zfmisc_1(A_1001,B_1000)))
      | ~ v1_funct_1(E_996) ) ),
    inference(resolution,[status(thm)],[c_106,c_42310])).

tff(c_42481,plain,(
    ! [A_1003,B_1004,E_1005] :
      ( k1_partfun1(A_1003,B_1004,'#skF_2','#skF_1',E_1005,'#skF_4') = k5_relat_1(E_1005,'#skF_4')
      | ~ m1_subset_1(E_1005,k1_zfmisc_1(k2_zfmisc_1(A_1003,B_1004)))
      | ~ v1_funct_1(E_1005) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_42316])).

tff(c_42487,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_42481])).

tff(c_42494,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_26167,c_42487])).

tff(c_375,plain,(
    ! [B_90] :
      ( k5_relat_1(k4_relat_1(B_90),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_90))
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_357])).

tff(c_397,plain,(
    ! [B_90] :
      ( k5_relat_1(k4_relat_1(B_90),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_375])).

tff(c_34628,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34583,c_397])).

tff(c_34675,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_34628])).

tff(c_42501,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k4_relat_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42494,c_34675])).

tff(c_42505,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_42501])).

tff(c_52,plain,(
    ! [A_24,B_26] :
      ( k2_funct_1(A_24) = B_26
      | k6_relat_1(k2_relat_1(A_24)) != k5_relat_1(B_26,A_24)
      | k2_relat_1(B_26) != k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_117,plain,(
    ! [A_24,B_26] :
      ( k2_funct_1(A_24) = B_26
      | k6_partfun1(k2_relat_1(A_24)) != k5_relat_1(B_26,A_24)
      | k2_relat_1(B_26) != k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52])).

tff(c_42527,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = k2_funct_1('#skF_4')
    | k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) != k6_partfun1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42505,c_117])).

tff(c_42542,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k2_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_20936,c_34685,c_20946,c_20999,c_20947,c_20953,c_42527])).

tff(c_45330,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44391,c_44402,c_42948,c_42542])).

tff(c_34640,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_34583,c_8])).

tff(c_34683,plain,(
    k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_34640])).

tff(c_30,plain,(
    ! [A_17] :
      ( v2_funct_1(k2_funct_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44432,plain,(
    ! [A_1032] :
      ( k4_relat_1(k2_funct_1(A_1032)) = k2_funct_1(k2_funct_1(A_1032))
      | ~ v1_funct_1(k2_funct_1(A_1032))
      | ~ v1_relat_1(k2_funct_1(A_1032))
      | ~ v2_funct_1(A_1032)
      | ~ v1_funct_1(A_1032)
      | ~ v1_relat_1(A_1032) ) ),
    inference(resolution,[status(thm)],[c_30,c_247])).

tff(c_44438,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = k2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34685,c_44432])).

tff(c_44452,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_110,c_34577,c_44391,c_34683,c_44438])).

tff(c_45337,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45330,c_44452])).

tff(c_45358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_45337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:06:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.87/8.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.87/8.20  
% 15.87/8.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.87/8.21  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.87/8.21  
% 15.87/8.21  %Foreground sorts:
% 15.87/8.21  
% 15.87/8.21  
% 15.87/8.21  %Background operators:
% 15.87/8.21  
% 15.87/8.21  
% 15.87/8.21  %Foreground operators:
% 15.87/8.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 15.87/8.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.87/8.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 15.87/8.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 15.87/8.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.87/8.21  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 15.87/8.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.87/8.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.87/8.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.87/8.21  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.87/8.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.87/8.21  tff('#skF_2', type, '#skF_2': $i).
% 15.87/8.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 15.87/8.21  tff('#skF_3', type, '#skF_3': $i).
% 15.87/8.21  tff('#skF_1', type, '#skF_1': $i).
% 15.87/8.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.87/8.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.87/8.21  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 15.87/8.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.87/8.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.87/8.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.87/8.21  tff('#skF_4', type, '#skF_4': $i).
% 15.87/8.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.87/8.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.87/8.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.87/8.21  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 15.87/8.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.87/8.21  
% 15.87/8.24  tff(f_271, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 15.87/8.24  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.87/8.24  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.87/8.24  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 15.87/8.24  tff(f_229, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 15.87/8.24  tff(f_213, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 15.87/8.24  tff(f_79, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 15.87/8.24  tff(f_159, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.87/8.24  tff(f_185, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 15.87/8.24  tff(f_211, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 15.87/8.24  tff(f_201, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 15.87/8.24  tff(f_167, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 15.87/8.24  tff(f_197, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 15.87/8.24  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 15.87/8.24  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 15.87/8.24  tff(f_55, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 15.87/8.24  tff(f_138, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 15.87/8.24  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 15.87/8.24  tff(f_36, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 15.87/8.24  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 15.87/8.24  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 15.87/8.24  tff(f_245, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 15.87/8.24  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 15.87/8.24  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 15.87/8.24  tff(f_155, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 15.87/8.24  tff(f_91, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 15.87/8.24  tff(c_94, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.87/8.24  tff(c_106, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_218, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.87/8.24  tff(c_227, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_106, c_218])).
% 15.87/8.24  tff(c_236, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_227])).
% 15.87/8.24  tff(c_110, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_22, plain, (![A_15]: (v1_funct_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.87/8.24  tff(c_108, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_26440, plain, (![C_724, A_725, B_726]: (v1_funct_1(k2_funct_1(C_724)) | k2_relset_1(A_725, B_726, C_724)!=B_726 | ~v2_funct_1(C_724) | ~m1_subset_1(C_724, k1_zfmisc_1(k2_zfmisc_1(A_725, B_726))) | ~v1_funct_2(C_724, A_725, B_726) | ~v1_funct_1(C_724))), inference(cnfTransformation, [status(thm)], [f_229])).
% 15.87/8.24  tff(c_26449, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_26440])).
% 15.87/8.24  tff(c_26458, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_26449])).
% 15.87/8.24  tff(c_26459, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_26458])).
% 15.87/8.24  tff(c_112, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_224, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_112, c_218])).
% 15.87/8.24  tff(c_233, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_224])).
% 15.87/8.24  tff(c_116, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_82, plain, (![A_50]: (k6_relat_1(A_50)=k6_partfun1(A_50))), inference(cnfTransformation, [status(thm)], [f_213])).
% 15.87/8.24  tff(c_28, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 15.87/8.24  tff(c_120, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_28])).
% 15.87/8.24  tff(c_98, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_325, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_159])).
% 15.87/8.24  tff(c_338, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_106, c_325])).
% 15.87/8.24  tff(c_20523, plain, (![B_634, A_635, C_636]: (k1_xboole_0=B_634 | k1_relset_1(A_635, B_634, C_636)=A_635 | ~v1_funct_2(C_636, A_635, B_634) | ~m1_subset_1(C_636, k1_zfmisc_1(k2_zfmisc_1(A_635, B_634))))), inference(cnfTransformation, [status(thm)], [f_185])).
% 15.87/8.24  tff(c_20532, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_106, c_20523])).
% 15.87/8.24  tff(c_20541, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_338, c_20532])).
% 15.87/8.24  tff(c_20542, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_98, c_20541])).
% 15.87/8.24  tff(c_24810, plain, (![C_699, B_700, A_701, D_698, E_696, F_697]: (k1_partfun1(A_701, B_700, C_699, D_698, E_696, F_697)=k5_relat_1(E_696, F_697) | ~m1_subset_1(F_697, k1_zfmisc_1(k2_zfmisc_1(C_699, D_698))) | ~v1_funct_1(F_697) | ~m1_subset_1(E_696, k1_zfmisc_1(k2_zfmisc_1(A_701, B_700))) | ~v1_funct_1(E_696))), inference(cnfTransformation, [status(thm)], [f_211])).
% 15.87/8.24  tff(c_24816, plain, (![A_701, B_700, E_696]: (k1_partfun1(A_701, B_700, '#skF_2', '#skF_1', E_696, '#skF_4')=k5_relat_1(E_696, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_696, k1_zfmisc_1(k2_zfmisc_1(A_701, B_700))) | ~v1_funct_1(E_696))), inference(resolution, [status(thm)], [c_106, c_24810])).
% 15.87/8.24  tff(c_24825, plain, (![A_702, B_703, E_704]: (k1_partfun1(A_702, B_703, '#skF_2', '#skF_1', E_704, '#skF_4')=k5_relat_1(E_704, '#skF_4') | ~m1_subset_1(E_704, k1_zfmisc_1(k2_zfmisc_1(A_702, B_703))) | ~v1_funct_1(E_704))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_24816])).
% 15.87/8.24  tff(c_24831, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_24825])).
% 15.87/8.24  tff(c_24838, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_24831])).
% 15.87/8.24  tff(c_78, plain, (![A_43]: (m1_subset_1(k6_partfun1(A_43), k1_zfmisc_1(k2_zfmisc_1(A_43, A_43))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 15.87/8.24  tff(c_102, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_21493, plain, (![D_648, C_649, A_650, B_651]: (D_648=C_649 | ~r2_relset_1(A_650, B_651, C_649, D_648) | ~m1_subset_1(D_648, k1_zfmisc_1(k2_zfmisc_1(A_650, B_651))) | ~m1_subset_1(C_649, k1_zfmisc_1(k2_zfmisc_1(A_650, B_651))))), inference(cnfTransformation, [status(thm)], [f_167])).
% 15.87/8.24  tff(c_21501, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_102, c_21493])).
% 15.87/8.24  tff(c_21516, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_21501])).
% 15.87/8.24  tff(c_21868, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_21516])).
% 15.87/8.24  tff(c_25789, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24838, c_21868])).
% 15.87/8.24  tff(c_26088, plain, (![D_717, E_718, F_716, C_719, B_715, A_714]: (m1_subset_1(k1_partfun1(A_714, B_715, C_719, D_717, E_718, F_716), k1_zfmisc_1(k2_zfmisc_1(A_714, D_717))) | ~m1_subset_1(F_716, k1_zfmisc_1(k2_zfmisc_1(C_719, D_717))) | ~v1_funct_1(F_716) | ~m1_subset_1(E_718, k1_zfmisc_1(k2_zfmisc_1(A_714, B_715))) | ~v1_funct_1(E_718))), inference(cnfTransformation, [status(thm)], [f_197])).
% 15.87/8.24  tff(c_26140, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24838, c_26088])).
% 15.87/8.24  tff(c_26164, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_112, c_110, c_106, c_26140])).
% 15.87/8.24  tff(c_26166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25789, c_26164])).
% 15.87/8.24  tff(c_26167, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_21516])).
% 15.87/8.24  tff(c_30309, plain, (![A_779, B_778, E_774, F_775, D_776, C_777]: (k1_partfun1(A_779, B_778, C_777, D_776, E_774, F_775)=k5_relat_1(E_774, F_775) | ~m1_subset_1(F_775, k1_zfmisc_1(k2_zfmisc_1(C_777, D_776))) | ~v1_funct_1(F_775) | ~m1_subset_1(E_774, k1_zfmisc_1(k2_zfmisc_1(A_779, B_778))) | ~v1_funct_1(E_774))), inference(cnfTransformation, [status(thm)], [f_211])).
% 15.87/8.24  tff(c_30315, plain, (![A_779, B_778, E_774]: (k1_partfun1(A_779, B_778, '#skF_2', '#skF_1', E_774, '#skF_4')=k5_relat_1(E_774, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_774, k1_zfmisc_1(k2_zfmisc_1(A_779, B_778))) | ~v1_funct_1(E_774))), inference(resolution, [status(thm)], [c_106, c_30309])).
% 15.87/8.24  tff(c_34301, plain, (![A_840, B_841, E_842]: (k1_partfun1(A_840, B_841, '#skF_2', '#skF_1', E_842, '#skF_4')=k5_relat_1(E_842, '#skF_4') | ~m1_subset_1(E_842, k1_zfmisc_1(k2_zfmisc_1(A_840, B_841))) | ~v1_funct_1(E_842))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_30315])).
% 15.87/8.24  tff(c_34310, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_34301])).
% 15.87/8.24  tff(c_34318, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_26167, c_34310])).
% 15.87/8.24  tff(c_36, plain, (![A_18, B_20]: (v2_funct_1(A_18) | k2_relat_1(B_20)!=k1_relat_1(A_18) | ~v2_funct_1(k5_relat_1(B_20, A_18)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.87/8.24  tff(c_34339, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34318, c_36])).
% 15.87/8.24  tff(c_34350, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_110, c_233, c_116, c_120, c_20542, c_34339])).
% 15.87/8.24  tff(c_34351, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_26459, c_34350])).
% 15.87/8.24  tff(c_14, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.87/8.24  tff(c_124, plain, (![A_11]: (k2_relat_1(k6_partfun1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_14])).
% 15.87/8.24  tff(c_96, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_114, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_104, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_100, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_271])).
% 15.87/8.24  tff(c_16, plain, (![A_12]: (k4_relat_1(k6_relat_1(A_12))=k6_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.87/8.24  tff(c_123, plain, (![A_12]: (k4_relat_1(k6_partfun1(A_12))=k6_partfun1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_16])).
% 15.87/8.24  tff(c_48, plain, (![A_23]: (k5_relat_1(k2_funct_1(A_23), A_23)=k6_relat_1(k2_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_138])).
% 15.87/8.24  tff(c_536, plain, (![A_96]: (k5_relat_1(k2_funct_1(A_96), A_96)=k6_partfun1(k2_relat_1(A_96)) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_48])).
% 15.87/8.24  tff(c_247, plain, (![A_77]: (k4_relat_1(A_77)=k2_funct_1(A_77) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.87/8.24  tff(c_256, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_100, c_247])).
% 15.87/8.24  tff(c_263, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_116, c_256])).
% 15.87/8.24  tff(c_4, plain, (![A_4]: (v1_relat_1(k4_relat_1(A_4)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.87/8.24  tff(c_270, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_263, c_4])).
% 15.87/8.24  tff(c_276, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_270])).
% 15.87/8.24  tff(c_8, plain, (![A_7]: (k4_relat_1(k4_relat_1(A_7))=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.87/8.24  tff(c_267, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_263, c_8])).
% 15.87/8.24  tff(c_274, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_233, c_267])).
% 15.87/8.24  tff(c_357, plain, (![B_90, A_91]: (k5_relat_1(k4_relat_1(B_90), k4_relat_1(A_91))=k4_relat_1(k5_relat_1(A_91, B_90)) | ~v1_relat_1(B_90) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.87/8.24  tff(c_372, plain, (![A_91]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_91))=k4_relat_1(k5_relat_1(A_91, '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_263, c_357])).
% 15.87/8.24  tff(c_402, plain, (![A_92]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_92))=k4_relat_1(k5_relat_1(A_92, '#skF_3')) | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_372])).
% 15.87/8.24  tff(c_411, plain, (k4_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_402])).
% 15.87/8.24  tff(c_424, plain, (k4_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_411])).
% 15.87/8.24  tff(c_542, plain, (k4_relat_1(k6_partfun1(k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_536, c_424])).
% 15.87/8.24  tff(c_548, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_116, c_100, c_123, c_542])).
% 15.87/8.24  tff(c_34402, plain, (![B_843, C_844, A_845]: (k6_partfun1(B_843)=k5_relat_1(k2_funct_1(C_844), C_844) | k1_xboole_0=B_843 | ~v2_funct_1(C_844) | k2_relset_1(A_845, B_843, C_844)!=B_843 | ~m1_subset_1(C_844, k1_zfmisc_1(k2_zfmisc_1(A_845, B_843))) | ~v1_funct_2(C_844, A_845, B_843) | ~v1_funct_1(C_844))), inference(cnfTransformation, [status(thm)], [f_245])).
% 15.87/8.24  tff(c_34408, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_34402])).
% 15.87/8.24  tff(c_34417, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_104, c_100, c_548, c_34408])).
% 15.87/8.24  tff(c_34418, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_96, c_34417])).
% 15.87/8.24  tff(c_34528, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34418, c_124])).
% 15.87/8.24  tff(c_34573, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_34528])).
% 15.87/8.24  tff(c_34575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34351, c_34573])).
% 15.87/8.24  tff(c_34577, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_26458])).
% 15.87/8.24  tff(c_20, plain, (![A_14]: (k4_relat_1(A_14)=k2_funct_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.87/8.24  tff(c_34580, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34577, c_20])).
% 15.87/8.24  tff(c_34583, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_110, c_34580])).
% 15.87/8.24  tff(c_34643, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34583, c_4])).
% 15.87/8.24  tff(c_34685, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_34643])).
% 15.87/8.24  tff(c_119, plain, (![A_23]: (k5_relat_1(k2_funct_1(A_23), A_23)=k6_partfun1(k2_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_48])).
% 15.87/8.24  tff(c_43449, plain, (![A_1025, B_1026]: (k4_relat_1(k5_relat_1(k4_relat_1(A_1025), B_1026))=k5_relat_1(k4_relat_1(B_1026), A_1025) | ~v1_relat_1(B_1026) | ~v1_relat_1(k4_relat_1(A_1025)) | ~v1_relat_1(A_1025))), inference(superposition, [status(thm), theory('equality')], [c_8, c_357])).
% 15.87/8.24  tff(c_43574, plain, (![B_1026]: (k4_relat_1(k5_relat_1(k2_funct_1('#skF_4'), B_1026))=k5_relat_1(k4_relat_1(B_1026), '#skF_4') | ~v1_relat_1(B_1026) | ~v1_relat_1(k4_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_34583, c_43449])).
% 15.87/8.24  tff(c_44180, plain, (![B_1030]: (k4_relat_1(k5_relat_1(k2_funct_1('#skF_4'), B_1030))=k5_relat_1(k4_relat_1(B_1030), '#skF_4') | ~v1_relat_1(B_1030))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_34685, c_34583, c_43574])).
% 15.87/8.24  tff(c_44303, plain, (k4_relat_1(k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k4_relat_1('#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_119, c_44180])).
% 15.87/8.24  tff(c_44334, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1(k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_110, c_34577, c_236, c_123, c_34583, c_44303])).
% 15.87/8.24  tff(c_38, plain, (![B_20, A_18]: (v2_funct_1(B_20) | k2_relat_1(B_20)!=k1_relat_1(A_18) | ~v2_funct_1(k5_relat_1(B_20, A_18)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.87/8.24  tff(c_44356, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1(k2_relat_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_44334, c_38])).
% 15.87/8.24  tff(c_44374, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_110, c_34685, c_120, c_20542, c_44356])).
% 15.87/8.24  tff(c_44382, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_44374])).
% 15.87/8.24  tff(c_44385, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_44382])).
% 15.87/8.24  tff(c_44389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_110, c_44385])).
% 15.87/8.24  tff(c_44391, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_44374])).
% 15.87/8.24  tff(c_40, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_118])).
% 15.87/8.24  tff(c_44390, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2' | v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_44374])).
% 15.87/8.24  tff(c_44394, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_44390])).
% 15.87/8.24  tff(c_44397, plain, (k1_relat_1('#skF_4')!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_44394])).
% 15.87/8.24  tff(c_44400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_110, c_34577, c_20542, c_44397])).
% 15.87/8.24  tff(c_44402, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_44390])).
% 15.87/8.24  tff(c_42773, plain, (![B_1013, C_1014, A_1015]: (k6_partfun1(B_1013)=k5_relat_1(k2_funct_1(C_1014), C_1014) | k1_xboole_0=B_1013 | ~v2_funct_1(C_1014) | k2_relset_1(A_1015, B_1013, C_1014)!=B_1013 | ~m1_subset_1(C_1014, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1013))) | ~v1_funct_2(C_1014, A_1015, B_1013) | ~v1_funct_1(C_1014))), inference(cnfTransformation, [status(thm)], [f_245])).
% 15.87/8.24  tff(c_42779, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_42773])).
% 15.87/8.24  tff(c_42788, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_114, c_104, c_100, c_548, c_42779])).
% 15.87/8.24  tff(c_42789, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_96, c_42788])).
% 15.87/8.24  tff(c_42902, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42789, c_124])).
% 15.87/8.24  tff(c_42948, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_42902])).
% 15.87/8.24  tff(c_337, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_325])).
% 15.87/8.24  tff(c_20529, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_112, c_20523])).
% 15.87/8.24  tff(c_20537, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_337, c_20529])).
% 15.87/8.24  tff(c_20538, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_96, c_20537])).
% 15.87/8.24  tff(c_20813, plain, (![B_639, A_640]: (v2_funct_1(B_639) | k2_relat_1(B_639)!=k1_relat_1(A_640) | ~v2_funct_1(k5_relat_1(B_639, A_640)) | ~v1_funct_1(B_639) | ~v1_relat_1(B_639) | ~v1_funct_1(A_640) | ~v1_relat_1(A_640))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.87/8.24  tff(c_20855, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k6_partfun1(k2_relat_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_548, c_20813])).
% 15.87/8.24  tff(c_20910, plain, (v2_funct_1(k2_funct_1('#skF_3')) | k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1' | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_116, c_276, c_120, c_20538, c_20855])).
% 15.87/8.24  tff(c_20927, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_20910])).
% 15.87/8.24  tff(c_20930, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_20927])).
% 15.87/8.24  tff(c_20934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_116, c_20930])).
% 15.87/8.24  tff(c_20936, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_20910])).
% 15.87/8.24  tff(c_20935, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1' | v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_20910])).
% 15.87/8.24  tff(c_20939, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_20935])).
% 15.87/8.24  tff(c_20942, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_20939])).
% 15.87/8.24  tff(c_20945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_116, c_100, c_20538, c_20942])).
% 15.87/8.24  tff(c_20946, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_20935])).
% 15.87/8.24  tff(c_20950, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_20946, c_20])).
% 15.87/8.24  tff(c_20953, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_276, c_20936, c_274, c_20950])).
% 15.87/8.24  tff(c_44, plain, (![A_22]: (k2_relat_1(k5_relat_1(A_22, k2_funct_1(A_22)))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_128])).
% 15.87/8.24  tff(c_20971, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20953, c_44])).
% 15.87/8.24  tff(c_20999, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_20936, c_20946, c_124, c_548, c_20971])).
% 15.87/8.24  tff(c_20947, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_20935])).
% 15.87/8.24  tff(c_42310, plain, (![B_1000, D_998, E_996, C_999, A_1001, F_997]: (k1_partfun1(A_1001, B_1000, C_999, D_998, E_996, F_997)=k5_relat_1(E_996, F_997) | ~m1_subset_1(F_997, k1_zfmisc_1(k2_zfmisc_1(C_999, D_998))) | ~v1_funct_1(F_997) | ~m1_subset_1(E_996, k1_zfmisc_1(k2_zfmisc_1(A_1001, B_1000))) | ~v1_funct_1(E_996))), inference(cnfTransformation, [status(thm)], [f_211])).
% 15.87/8.24  tff(c_42316, plain, (![A_1001, B_1000, E_996]: (k1_partfun1(A_1001, B_1000, '#skF_2', '#skF_1', E_996, '#skF_4')=k5_relat_1(E_996, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_996, k1_zfmisc_1(k2_zfmisc_1(A_1001, B_1000))) | ~v1_funct_1(E_996))), inference(resolution, [status(thm)], [c_106, c_42310])).
% 15.87/8.24  tff(c_42481, plain, (![A_1003, B_1004, E_1005]: (k1_partfun1(A_1003, B_1004, '#skF_2', '#skF_1', E_1005, '#skF_4')=k5_relat_1(E_1005, '#skF_4') | ~m1_subset_1(E_1005, k1_zfmisc_1(k2_zfmisc_1(A_1003, B_1004))) | ~v1_funct_1(E_1005))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_42316])).
% 15.87/8.24  tff(c_42487, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_42481])).
% 15.87/8.24  tff(c_42494, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_26167, c_42487])).
% 15.87/8.24  tff(c_375, plain, (![B_90]: (k5_relat_1(k4_relat_1(B_90), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_90)) | ~v1_relat_1(B_90) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_357])).
% 15.87/8.24  tff(c_397, plain, (![B_90]: (k5_relat_1(k4_relat_1(B_90), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_90)) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_375])).
% 15.87/8.24  tff(c_34628, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34583, c_397])).
% 15.87/8.24  tff(c_34675, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_34628])).
% 15.87/8.24  tff(c_42501, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k4_relat_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42494, c_34675])).
% 15.87/8.24  tff(c_42505, plain, (k5_relat_1(k2_funct_1('#skF_4'), k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_42501])).
% 15.87/8.24  tff(c_52, plain, (![A_24, B_26]: (k2_funct_1(A_24)=B_26 | k6_relat_1(k2_relat_1(A_24))!=k5_relat_1(B_26, A_24) | k2_relat_1(B_26)!=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_155])).
% 15.87/8.24  tff(c_117, plain, (![A_24, B_26]: (k2_funct_1(A_24)=B_26 | k6_partfun1(k2_relat_1(A_24))!=k5_relat_1(B_26, A_24) | k2_relat_1(B_26)!=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52])).
% 15.87/8.24  tff(c_42527, plain, (k2_funct_1(k2_funct_1('#skF_3'))=k2_funct_1('#skF_4') | k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))!=k6_partfun1('#skF_1') | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42505, c_117])).
% 15.87/8.24  tff(c_42542, plain, (k2_funct_1('#skF_4')='#skF_3' | k2_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_20936, c_34685, c_20946, c_20999, c_20947, c_20953, c_42527])).
% 15.87/8.24  tff(c_45330, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44391, c_44402, c_42948, c_42542])).
% 15.87/8.24  tff(c_34640, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_34583, c_8])).
% 15.87/8.24  tff(c_34683, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_34640])).
% 15.87/8.24  tff(c_30, plain, (![A_17]: (v2_funct_1(k2_funct_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_91])).
% 15.87/8.24  tff(c_44432, plain, (![A_1032]: (k4_relat_1(k2_funct_1(A_1032))=k2_funct_1(k2_funct_1(A_1032)) | ~v1_funct_1(k2_funct_1(A_1032)) | ~v1_relat_1(k2_funct_1(A_1032)) | ~v2_funct_1(A_1032) | ~v1_funct_1(A_1032) | ~v1_relat_1(A_1032))), inference(resolution, [status(thm)], [c_30, c_247])).
% 15.87/8.24  tff(c_44438, plain, (k4_relat_1(k2_funct_1('#skF_4'))=k2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34685, c_44432])).
% 15.87/8.24  tff(c_44452, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_110, c_34577, c_44391, c_34683, c_44438])).
% 15.87/8.24  tff(c_45337, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45330, c_44452])).
% 15.87/8.24  tff(c_45358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_45337])).
% 15.87/8.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.87/8.24  
% 15.87/8.24  Inference rules
% 15.87/8.24  ----------------------
% 15.87/8.24  #Ref     : 0
% 15.87/8.24  #Sup     : 10860
% 15.87/8.24  #Fact    : 0
% 15.87/8.24  #Define  : 0
% 15.87/8.24  #Split   : 100
% 15.87/8.24  #Chain   : 0
% 15.87/8.24  #Close   : 0
% 15.87/8.24  
% 15.87/8.24  Ordering : KBO
% 15.87/8.24  
% 15.87/8.24  Simplification rules
% 15.87/8.24  ----------------------
% 15.87/8.24  #Subsume      : 1299
% 15.87/8.24  #Demod        : 16416
% 15.87/8.24  #Tautology    : 3912
% 15.87/8.24  #SimpNegUnit  : 308
% 15.87/8.24  #BackRed      : 228
% 15.87/8.24  
% 15.87/8.24  #Partial instantiations: 0
% 15.87/8.24  #Strategies tried      : 1
% 15.87/8.24  
% 15.87/8.24  Timing (in seconds)
% 15.87/8.24  ----------------------
% 15.87/8.24  Preprocessing        : 0.40
% 15.87/8.24  Parsing              : 0.20
% 15.87/8.24  CNF conversion       : 0.03
% 15.87/8.24  Main loop            : 6.89
% 15.87/8.24  Inferencing          : 1.44
% 15.87/8.24  Reduction            : 3.43
% 15.87/8.24  Demodulation         : 2.83
% 15.87/8.24  BG Simplification    : 0.19
% 15.87/8.24  Subsumption          : 1.47
% 15.87/8.24  Abstraction          : 0.30
% 15.87/8.24  MUC search           : 0.00
% 15.87/8.24  Cooper               : 0.00
% 15.87/8.24  Total                : 7.37
% 15.87/8.24  Index Insertion      : 0.00
% 15.87/8.24  Index Deletion       : 0.00
% 15.87/8.24  Index Matching       : 0.00
% 15.87/8.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
