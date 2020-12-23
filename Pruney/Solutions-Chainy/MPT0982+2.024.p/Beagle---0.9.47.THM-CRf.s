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
% DateTime   : Thu Dec  3 10:11:58 EST 2020

% Result     : Theorem 6.76s
% Output     : CNFRefutation 6.76s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 536 expanded)
%              Number of leaves         :   45 ( 205 expanded)
%              Depth                    :   19
%              Number of atoms          :  254 (1751 expanded)
%              Number of equality atoms :   78 ( 474 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_171,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_4650,plain,(
    ! [C_349,B_350,F_347,E_346,D_348,A_351] :
      ( k1_partfun1(A_351,B_350,C_349,D_348,E_346,F_347) = k5_relat_1(E_346,F_347)
      | ~ m1_subset_1(F_347,k1_zfmisc_1(k2_zfmisc_1(C_349,D_348)))
      | ~ v1_funct_1(F_347)
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_351,B_350)))
      | ~ v1_funct_1(E_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_4654,plain,(
    ! [A_351,B_350,E_346] :
      ( k1_partfun1(A_351,B_350,'#skF_2','#skF_3',E_346,'#skF_5') = k5_relat_1(E_346,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_346,k1_zfmisc_1(k2_zfmisc_1(A_351,B_350)))
      | ~ v1_funct_1(E_346) ) ),
    inference(resolution,[status(thm)],[c_64,c_4650])).

tff(c_4835,plain,(
    ! [A_364,B_365,E_366] :
      ( k1_partfun1(A_364,B_365,'#skF_2','#skF_3',E_366,'#skF_5') = k5_relat_1(E_366,'#skF_5')
      | ~ m1_subset_1(E_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365)))
      | ~ v1_funct_1(E_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4654])).

tff(c_4844,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_4835])).

tff(c_4854,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4844])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_5584,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4854,c_62])).

tff(c_50,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] :
      ( m1_subset_1(k1_partfun1(A_38,B_39,C_40,D_41,E_42,F_43),k1_zfmisc_1(k2_zfmisc_1(A_38,D_41)))
      | ~ m1_subset_1(F_43,k1_zfmisc_1(k2_zfmisc_1(C_40,D_41)))
      | ~ v1_funct_1(F_43)
      | ~ m1_subset_1(E_42,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_1(E_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5588,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4854,c_50])).

tff(c_5592,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_5588])).

tff(c_36,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_relset_1(A_32,B_33,C_34) = k2_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5622,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_5592,c_36])).

tff(c_5660,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5584,c_5622])).

tff(c_3358,plain,(
    ! [A_266,B_267,C_268] :
      ( k2_relset_1(A_266,B_267,C_268) = k2_relat_1(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3365,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3358])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_3367,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3365,c_56])).

tff(c_93,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_93])).

tff(c_121,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_128,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_121])).

tff(c_101,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_93])).

tff(c_60,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_292,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_300,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_292])).

tff(c_3994,plain,(
    ! [B_306,A_307,C_308] :
      ( k1_xboole_0 = B_306
      | k1_relset_1(A_307,B_306,C_308) = A_307
      | ~ v1_funct_2(C_308,A_307,B_306)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(k2_zfmisc_1(A_307,B_306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4000,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_3994])).

tff(c_4006,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_300,c_4000])).

tff(c_4007,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4006])).

tff(c_4296,plain,(
    ! [A_326,B_327] :
      ( r1_tarski(k1_relat_1(A_326),k2_relat_1(B_327))
      | ~ v2_funct_1(A_326)
      | k2_relat_1(k5_relat_1(B_327,A_326)) != k2_relat_1(A_326)
      | ~ v1_funct_1(B_327)
      | ~ v1_relat_1(B_327)
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4318,plain,(
    ! [B_327] :
      ( r1_tarski('#skF_2',k2_relat_1(B_327))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_327,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_327)
      | ~ v1_relat_1(B_327)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4007,c_4296])).

tff(c_4478,plain,(
    ! [B_330] :
      ( r1_tarski('#skF_2',k2_relat_1(B_330))
      | k2_relat_1(k5_relat_1(B_330,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_330)
      | ~ v1_relat_1(B_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_68,c_60,c_4318])).

tff(c_130,plain,(
    ! [C_72,A_73,B_74] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_137,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_130])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_152,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_24])).

tff(c_155,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_152])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_165,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_20])).

tff(c_169,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_165])).

tff(c_139,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(k2_relat_1(B_75),A_76)
      | ~ v5_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4106,plain,(
    ! [B_317,A_318,A_319] :
      ( r1_tarski(k9_relat_1(B_317,A_318),A_319)
      | ~ v5_relat_1(k7_relat_1(B_317,A_318),A_319)
      | ~ v1_relat_1(k7_relat_1(B_317,A_318))
      | ~ v1_relat_1(B_317) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_139])).

tff(c_4115,plain,(
    ! [A_319] :
      ( r1_tarski(k9_relat_1('#skF_4','#skF_1'),A_319)
      | ~ v5_relat_1('#skF_4',A_319)
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_1'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_4106])).

tff(c_4163,plain,(
    ! [A_321] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_321)
      | ~ v5_relat_1('#skF_4',A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_100,c_155,c_169,c_4115])).

tff(c_78,plain,(
    ! [A_56,B_57] :
      ( r2_xboole_0(A_56,B_57)
      | B_57 = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [B_57,A_56] :
      ( ~ r1_tarski(B_57,A_56)
      | B_57 = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_78,c_8])).

tff(c_4201,plain,(
    ! [A_321] :
      ( k2_relat_1('#skF_4') = A_321
      | ~ r1_tarski(A_321,k2_relat_1('#skF_4'))
      | ~ v5_relat_1('#skF_4',A_321) ) ),
    inference(resolution,[status(thm)],[c_4163,c_90])).

tff(c_4482,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4478,c_4201])).

tff(c_4527,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_74,c_128,c_4482])).

tff(c_4528,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_3367,c_4527])).

tff(c_5727,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5660,c_4528])).

tff(c_129,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_121])).

tff(c_22,plain,(
    ! [B_17,A_15] :
      ( k9_relat_1(B_17,k2_relat_1(A_15)) = k2_relat_1(k5_relat_1(A_15,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_138,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_130])).

tff(c_158,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_138,c_24])).

tff(c_161,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_158])).

tff(c_174,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_20])).

tff(c_178,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_174])).

tff(c_537,plain,(
    ! [B_118,A_119,C_120] :
      ( k1_xboole_0 = B_118
      | k1_relset_1(A_119,B_118,C_120) = A_119
      | ~ v1_funct_2(C_120,A_119,B_118)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_543,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_537])).

tff(c_549,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_300,c_543])).

tff(c_550,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_549])).

tff(c_213,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k9_relat_1(B_81,A_82),k9_relat_1(B_81,k1_relat_1(B_81)))
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_218,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),k9_relat_1('#skF_5',k1_relat_1('#skF_5')))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_213])).

tff(c_224,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k9_relat_1('#skF_5',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_218])).

tff(c_555,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k9_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_224])).

tff(c_559,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_555])).

tff(c_242,plain,
    ( k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski(k9_relat_1('#skF_5',k1_relat_1('#skF_5')),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_224,c_90])).

tff(c_309,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k1_relat_1('#skF_5')),k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_551,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_309])).

tff(c_556,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_551])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_556])).

tff(c_797,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k2_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k9_relat_1(B_12,A_11),k9_relat_1(B_12,k1_relat_1(B_12)))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_808,plain,(
    ! [A_11] :
      ( r1_tarski(k9_relat_1('#skF_5',A_11),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_18])).

tff(c_3217,plain,(
    ! [A_261] : r1_tarski(k9_relat_1('#skF_5',A_261),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_808])).

tff(c_3226,plain,(
    ! [A_15] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_15,'#skF_5')),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3217])).

tff(c_3236,plain,(
    ! [A_15] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_15,'#skF_5')),k2_relat_1('#skF_5'))
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_3226])).

tff(c_3474,plain,(
    ! [B_274,A_275] :
      ( k2_relat_1(B_274) = A_275
      | ~ r1_tarski(A_275,k2_relat_1(B_274))
      | ~ v5_relat_1(B_274,A_275)
      | ~ v1_relat_1(B_274) ) ),
    inference(resolution,[status(thm)],[c_139,c_90])).

tff(c_3477,plain,(
    ! [A_15] :
      ( k2_relat_1(k5_relat_1(A_15,'#skF_5')) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_15,'#skF_5')))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_3236,c_3474])).

tff(c_3508,plain,(
    ! [A_15] :
      ( k2_relat_1(k5_relat_1(A_15,'#skF_5')) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_15,'#skF_5')))
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_3477])).

tff(c_5755,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5660,c_3508])).

tff(c_5809,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_129,c_5660,c_5755])).

tff(c_5834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5727,c_5809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.76/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.32  
% 6.76/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.76/2.32  
% 6.76/2.32  %Foreground sorts:
% 6.76/2.32  
% 6.76/2.32  
% 6.76/2.32  %Background operators:
% 6.76/2.32  
% 6.76/2.32  
% 6.76/2.32  %Foreground operators:
% 6.76/2.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.76/2.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 6.76/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.76/2.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.76/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.76/2.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.76/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.76/2.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.76/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.76/2.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.76/2.32  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.76/2.32  tff('#skF_5', type, '#skF_5': $i).
% 6.76/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.76/2.32  tff('#skF_2', type, '#skF_2': $i).
% 6.76/2.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.76/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.76/2.32  tff('#skF_1', type, '#skF_1': $i).
% 6.76/2.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.76/2.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.76/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.76/2.32  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.76/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.76/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.76/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.76/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.76/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.76/2.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.76/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.76/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.76/2.32  
% 6.76/2.34  tff(f_171, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 6.76/2.34  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.76/2.34  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.76/2.34  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.76/2.34  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.76/2.34  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.76/2.34  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.76/2.34  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.76/2.34  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_1)).
% 6.76/2.34  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.76/2.34  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.76/2.34  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.76/2.34  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.76/2.34  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 6.76/2.34  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 6.76/2.34  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 6.76/2.34  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_4650, plain, (![C_349, B_350, F_347, E_346, D_348, A_351]: (k1_partfun1(A_351, B_350, C_349, D_348, E_346, F_347)=k5_relat_1(E_346, F_347) | ~m1_subset_1(F_347, k1_zfmisc_1(k2_zfmisc_1(C_349, D_348))) | ~v1_funct_1(F_347) | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_351, B_350))) | ~v1_funct_1(E_346))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.76/2.34  tff(c_4654, plain, (![A_351, B_350, E_346]: (k1_partfun1(A_351, B_350, '#skF_2', '#skF_3', E_346, '#skF_5')=k5_relat_1(E_346, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_346, k1_zfmisc_1(k2_zfmisc_1(A_351, B_350))) | ~v1_funct_1(E_346))), inference(resolution, [status(thm)], [c_64, c_4650])).
% 6.76/2.34  tff(c_4835, plain, (![A_364, B_365, E_366]: (k1_partfun1(A_364, B_365, '#skF_2', '#skF_3', E_366, '#skF_5')=k5_relat_1(E_366, '#skF_5') | ~m1_subset_1(E_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))) | ~v1_funct_1(E_366))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4654])).
% 6.76/2.34  tff(c_4844, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_4835])).
% 6.76/2.34  tff(c_4854, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4844])).
% 6.76/2.34  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_5584, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4854, c_62])).
% 6.76/2.34  tff(c_50, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (m1_subset_1(k1_partfun1(A_38, B_39, C_40, D_41, E_42, F_43), k1_zfmisc_1(k2_zfmisc_1(A_38, D_41))) | ~m1_subset_1(F_43, k1_zfmisc_1(k2_zfmisc_1(C_40, D_41))) | ~v1_funct_1(F_43) | ~m1_subset_1(E_42, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_1(E_42))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.76/2.34  tff(c_5588, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4854, c_50])).
% 6.76/2.34  tff(c_5592, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_5588])).
% 6.76/2.34  tff(c_36, plain, (![A_32, B_33, C_34]: (k2_relset_1(A_32, B_33, C_34)=k2_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.76/2.34  tff(c_5622, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_5592, c_36])).
% 6.76/2.34  tff(c_5660, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5584, c_5622])).
% 6.76/2.34  tff(c_3358, plain, (![A_266, B_267, C_268]: (k2_relset_1(A_266, B_267, C_268)=k2_relat_1(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.76/2.34  tff(c_3365, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3358])).
% 6.76/2.34  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_3367, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3365, c_56])).
% 6.76/2.34  tff(c_93, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.76/2.34  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_93])).
% 6.76/2.34  tff(c_121, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.76/2.34  tff(c_128, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_121])).
% 6.76/2.34  tff(c_101, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_93])).
% 6.76/2.34  tff(c_60, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_171])).
% 6.76/2.34  tff(c_292, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.76/2.34  tff(c_300, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_292])).
% 6.76/2.34  tff(c_3994, plain, (![B_306, A_307, C_308]: (k1_xboole_0=B_306 | k1_relset_1(A_307, B_306, C_308)=A_307 | ~v1_funct_2(C_308, A_307, B_306) | ~m1_subset_1(C_308, k1_zfmisc_1(k2_zfmisc_1(A_307, B_306))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.76/2.34  tff(c_4000, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_3994])).
% 6.76/2.34  tff(c_4006, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_300, c_4000])).
% 6.76/2.34  tff(c_4007, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_4006])).
% 6.76/2.34  tff(c_4296, plain, (![A_326, B_327]: (r1_tarski(k1_relat_1(A_326), k2_relat_1(B_327)) | ~v2_funct_1(A_326) | k2_relat_1(k5_relat_1(B_327, A_326))!=k2_relat_1(A_326) | ~v1_funct_1(B_327) | ~v1_relat_1(B_327) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.76/2.34  tff(c_4318, plain, (![B_327]: (r1_tarski('#skF_2', k2_relat_1(B_327)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_327, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_327) | ~v1_relat_1(B_327) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4007, c_4296])).
% 6.76/2.34  tff(c_4478, plain, (![B_330]: (r1_tarski('#skF_2', k2_relat_1(B_330)) | k2_relat_1(k5_relat_1(B_330, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_330) | ~v1_relat_1(B_330))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_68, c_60, c_4318])).
% 6.76/2.34  tff(c_130, plain, (![C_72, A_73, B_74]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.76/2.34  tff(c_137, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_130])).
% 6.76/2.34  tff(c_24, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.76/2.34  tff(c_152, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_137, c_24])).
% 6.76/2.34  tff(c_155, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_152])).
% 6.76/2.34  tff(c_20, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.76/2.34  tff(c_165, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_155, c_20])).
% 6.76/2.34  tff(c_169, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_165])).
% 6.76/2.34  tff(c_139, plain, (![B_75, A_76]: (r1_tarski(k2_relat_1(B_75), A_76) | ~v5_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.76/2.34  tff(c_4106, plain, (![B_317, A_318, A_319]: (r1_tarski(k9_relat_1(B_317, A_318), A_319) | ~v5_relat_1(k7_relat_1(B_317, A_318), A_319) | ~v1_relat_1(k7_relat_1(B_317, A_318)) | ~v1_relat_1(B_317))), inference(superposition, [status(thm), theory('equality')], [c_20, c_139])).
% 6.76/2.34  tff(c_4115, plain, (![A_319]: (r1_tarski(k9_relat_1('#skF_4', '#skF_1'), A_319) | ~v5_relat_1('#skF_4', A_319) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_4106])).
% 6.76/2.34  tff(c_4163, plain, (![A_321]: (r1_tarski(k2_relat_1('#skF_4'), A_321) | ~v5_relat_1('#skF_4', A_321))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_100, c_155, c_169, c_4115])).
% 6.76/2.34  tff(c_78, plain, (![A_56, B_57]: (r2_xboole_0(A_56, B_57) | B_57=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.76/2.34  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.76/2.34  tff(c_90, plain, (![B_57, A_56]: (~r1_tarski(B_57, A_56) | B_57=A_56 | ~r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_78, c_8])).
% 6.76/2.34  tff(c_4201, plain, (![A_321]: (k2_relat_1('#skF_4')=A_321 | ~r1_tarski(A_321, k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', A_321))), inference(resolution, [status(thm)], [c_4163, c_90])).
% 6.76/2.34  tff(c_4482, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4478, c_4201])).
% 6.76/2.34  tff(c_4527, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_74, c_128, c_4482])).
% 6.76/2.34  tff(c_4528, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_3367, c_4527])).
% 6.76/2.34  tff(c_5727, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5660, c_4528])).
% 6.76/2.34  tff(c_129, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_121])).
% 6.76/2.34  tff(c_22, plain, (![B_17, A_15]: (k9_relat_1(B_17, k2_relat_1(A_15))=k2_relat_1(k5_relat_1(A_15, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.76/2.34  tff(c_138, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_130])).
% 6.76/2.34  tff(c_158, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_138, c_24])).
% 6.76/2.34  tff(c_161, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_158])).
% 6.76/2.34  tff(c_174, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_161, c_20])).
% 6.76/2.34  tff(c_178, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_174])).
% 6.76/2.34  tff(c_537, plain, (![B_118, A_119, C_120]: (k1_xboole_0=B_118 | k1_relset_1(A_119, B_118, C_120)=A_119 | ~v1_funct_2(C_120, A_119, B_118) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.76/2.34  tff(c_543, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_537])).
% 6.76/2.34  tff(c_549, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_300, c_543])).
% 6.76/2.34  tff(c_550, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_549])).
% 6.76/2.34  tff(c_213, plain, (![B_81, A_82]: (r1_tarski(k9_relat_1(B_81, A_82), k9_relat_1(B_81, k1_relat_1(B_81))) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.76/2.34  tff(c_218, plain, (r1_tarski(k2_relat_1('#skF_5'), k9_relat_1('#skF_5', k1_relat_1('#skF_5'))) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_178, c_213])).
% 6.76/2.34  tff(c_224, plain, (r1_tarski(k2_relat_1('#skF_5'), k9_relat_1('#skF_5', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_218])).
% 6.76/2.34  tff(c_555, plain, (r1_tarski(k2_relat_1('#skF_5'), k9_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_550, c_224])).
% 6.76/2.34  tff(c_559, plain, (r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_555])).
% 6.76/2.34  tff(c_242, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski(k9_relat_1('#skF_5', k1_relat_1('#skF_5')), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_224, c_90])).
% 6.76/2.34  tff(c_309, plain, (~r1_tarski(k9_relat_1('#skF_5', k1_relat_1('#skF_5')), k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_242])).
% 6.76/2.34  tff(c_551, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_550, c_309])).
% 6.76/2.34  tff(c_556, plain, (~r1_tarski(k2_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_551])).
% 6.76/2.34  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_559, c_556])).
% 6.76/2.34  tff(c_797, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k2_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_242])).
% 6.76/2.34  tff(c_18, plain, (![B_12, A_11]: (r1_tarski(k9_relat_1(B_12, A_11), k9_relat_1(B_12, k1_relat_1(B_12))) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.76/2.34  tff(c_808, plain, (![A_11]: (r1_tarski(k9_relat_1('#skF_5', A_11), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_797, c_18])).
% 6.76/2.34  tff(c_3217, plain, (![A_261]: (r1_tarski(k9_relat_1('#skF_5', A_261), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_808])).
% 6.76/2.34  tff(c_3226, plain, (![A_15]: (r1_tarski(k2_relat_1(k5_relat_1(A_15, '#skF_5')), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3217])).
% 6.76/2.34  tff(c_3236, plain, (![A_15]: (r1_tarski(k2_relat_1(k5_relat_1(A_15, '#skF_5')), k2_relat_1('#skF_5')) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_3226])).
% 6.76/2.34  tff(c_3474, plain, (![B_274, A_275]: (k2_relat_1(B_274)=A_275 | ~r1_tarski(A_275, k2_relat_1(B_274)) | ~v5_relat_1(B_274, A_275) | ~v1_relat_1(B_274))), inference(resolution, [status(thm)], [c_139, c_90])).
% 6.76/2.34  tff(c_3477, plain, (![A_15]: (k2_relat_1(k5_relat_1(A_15, '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_15, '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_3236, c_3474])).
% 6.76/2.34  tff(c_3508, plain, (![A_15]: (k2_relat_1(k5_relat_1(A_15, '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_15, '#skF_5'))) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_3477])).
% 6.76/2.34  tff(c_5755, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5660, c_3508])).
% 6.76/2.34  tff(c_5809, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_129, c_5660, c_5755])).
% 6.76/2.34  tff(c_5834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5727, c_5809])).
% 6.76/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.76/2.34  
% 6.76/2.34  Inference rules
% 6.76/2.34  ----------------------
% 6.76/2.34  #Ref     : 0
% 6.76/2.34  #Sup     : 1298
% 6.76/2.34  #Fact    : 0
% 6.76/2.34  #Define  : 0
% 6.76/2.34  #Split   : 13
% 6.76/2.34  #Chain   : 0
% 6.76/2.34  #Close   : 0
% 6.76/2.34  
% 6.76/2.34  Ordering : KBO
% 6.76/2.34  
% 6.76/2.34  Simplification rules
% 6.76/2.34  ----------------------
% 6.76/2.34  #Subsume      : 76
% 6.76/2.34  #Demod        : 1055
% 6.76/2.34  #Tautology    : 456
% 6.76/2.34  #SimpNegUnit  : 31
% 6.76/2.34  #BackRed      : 89
% 6.76/2.34  
% 6.76/2.34  #Partial instantiations: 0
% 6.76/2.34  #Strategies tried      : 1
% 6.76/2.34  
% 6.76/2.34  Timing (in seconds)
% 6.76/2.34  ----------------------
% 6.76/2.35  Preprocessing        : 0.36
% 6.76/2.35  Parsing              : 0.20
% 6.76/2.35  CNF conversion       : 0.02
% 6.76/2.35  Main loop            : 1.20
% 6.76/2.35  Inferencing          : 0.40
% 6.76/2.35  Reduction            : 0.44
% 6.76/2.35  Demodulation         : 0.32
% 6.76/2.35  BG Simplification    : 0.05
% 6.76/2.35  Subsumption          : 0.22
% 6.76/2.35  Abstraction          : 0.05
% 6.76/2.35  MUC search           : 0.00
% 6.76/2.35  Cooper               : 0.00
% 6.76/2.35  Total                : 1.61
% 6.76/2.35  Index Insertion      : 0.00
% 6.76/2.35  Index Deletion       : 0.00
% 6.76/2.35  Index Matching       : 0.00
% 6.76/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
