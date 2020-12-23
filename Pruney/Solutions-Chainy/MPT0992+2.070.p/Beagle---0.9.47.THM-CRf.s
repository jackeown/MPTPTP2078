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
% DateTime   : Thu Dec  3 10:13:41 EST 2020

% Result     : Theorem 8.87s
% Output     : CNFRefutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :  244 (9194 expanded)
%              Number of leaves         :   37 (2874 expanded)
%              Depth                    :   20
%              Number of atoms          :  428 (26594 expanded)
%              Number of equality atoms :  110 (11116 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_111,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_111])).

tff(c_121,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_117])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8884,plain,(
    ! [A_781,B_782,C_783] :
      ( k1_relset_1(A_781,B_782,C_783) = k1_relat_1(C_783)
      | ~ m1_subset_1(C_783,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8903,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_8884])).

tff(c_9461,plain,(
    ! [B_859,A_860,C_861] :
      ( k1_xboole_0 = B_859
      | k1_relset_1(A_860,B_859,C_861) = A_860
      | ~ v1_funct_2(C_861,A_860,B_859)
      | ~ m1_subset_1(C_861,k1_zfmisc_1(k2_zfmisc_1(A_860,B_859))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9474,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_9461])).

tff(c_9488,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8903,c_9474])).

tff(c_9489,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_9488])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9501,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9489,c_24])).

tff(c_9528,plain,(
    ! [A_864] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_864)) = A_864
      | ~ r1_tarski(A_864,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_9501])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_9309,plain,(
    ! [A_849,B_850,C_851,D_852] :
      ( k2_partfun1(A_849,B_850,C_851,D_852) = k7_relat_1(C_851,D_852)
      | ~ m1_subset_1(C_851,k1_zfmisc_1(k2_zfmisc_1(A_849,B_850)))
      | ~ v1_funct_1(C_851) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_9318,plain,(
    ! [D_852] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_852) = k7_relat_1('#skF_4',D_852)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_9309])).

tff(c_9330,plain,(
    ! [D_852] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_852) = k7_relat_1('#skF_4',D_852) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9318])).

tff(c_3135,plain,(
    ! [A_361,B_362,C_363,D_364] :
      ( k2_partfun1(A_361,B_362,C_363,D_364) = k7_relat_1(C_363,D_364)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_361,B_362)))
      | ~ v1_funct_1(C_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3142,plain,(
    ! [D_364] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_364) = k7_relat_1('#skF_4',D_364)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_3135])).

tff(c_3151,plain,(
    ! [D_364] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_364) = k7_relat_1('#skF_4',D_364) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3142])).

tff(c_3532,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( m1_subset_1(k2_partfun1(A_404,B_405,C_406,D_407),k1_zfmisc_1(k2_zfmisc_1(A_404,B_405)))
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_404,B_405)))
      | ~ v1_funct_1(C_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3560,plain,(
    ! [D_364] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_364),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3151,c_3532])).

tff(c_3592,plain,(
    ! [D_408] : m1_subset_1(k7_relat_1('#skF_4',D_408),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_3560])).

tff(c_26,plain,(
    ! [C_19,B_18,A_17] :
      ( v5_relat_1(C_19,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3634,plain,(
    ! [D_408] : v5_relat_1(k7_relat_1('#skF_4',D_408),'#skF_2') ),
    inference(resolution,[status(thm)],[c_3592,c_26])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3614,plain,(
    ! [D_408] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_408))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_3592,c_14])).

tff(c_3637,plain,(
    ! [D_408] : v1_relat_1(k7_relat_1('#skF_4',D_408)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3614])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2905,plain,(
    ! [A_329,B_330,C_331,D_332] :
      ( v1_funct_1(k2_partfun1(A_329,B_330,C_331,D_332))
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(A_329,B_330)))
      | ~ v1_funct_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2910,plain,(
    ! [D_332] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_332))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_2905])).

tff(c_2918,plain,(
    ! [D_332] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_332)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2910])).

tff(c_3152,plain,(
    ! [D_332] : v1_funct_1(k7_relat_1('#skF_4',D_332)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_2918])).

tff(c_936,plain,(
    ! [A_170,B_171,C_172] :
      ( k1_relset_1(A_170,B_171,C_172) = k1_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_951,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_936])).

tff(c_3370,plain,(
    ! [B_394,A_395,C_396] :
      ( k1_xboole_0 = B_394
      | k1_relset_1(A_395,B_394,C_396) = A_395
      | ~ v1_funct_2(C_396,A_395,B_394)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_3380,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_3370])).

tff(c_3391,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_951,c_3380])).

tff(c_3392,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3391])).

tff(c_3408,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3392,c_24])).

tff(c_3416,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_3408])).

tff(c_3025,plain,(
    ! [B_350,A_351] :
      ( m1_subset_1(B_350,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_350),A_351)))
      | ~ r1_tarski(k2_relat_1(B_350),A_351)
      | ~ v1_funct_1(B_350)
      | ~ v1_relat_1(B_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4727,plain,(
    ! [B_510,A_511] :
      ( r1_tarski(B_510,k2_zfmisc_1(k1_relat_1(B_510),A_511))
      | ~ r1_tarski(k2_relat_1(B_510),A_511)
      | ~ v1_funct_1(B_510)
      | ~ v1_relat_1(B_510) ) ),
    inference(resolution,[status(thm)],[c_3025,c_10])).

tff(c_4782,plain,(
    ! [A_15,A_511] :
      ( r1_tarski(k7_relat_1('#skF_4',A_15),k2_zfmisc_1(A_15,A_511))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_15)),A_511)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_15))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_15))
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3416,c_4727])).

tff(c_6031,plain,(
    ! [A_559,A_560] :
      ( r1_tarski(k7_relat_1('#skF_4',A_559),k2_zfmisc_1(A_559,A_560))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_559)),A_560)
      | ~ r1_tarski(A_559,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_3152,c_4782])).

tff(c_6041,plain,(
    ! [A_559,A_9] :
      ( r1_tarski(k7_relat_1('#skF_4',A_559),k2_zfmisc_1(A_559,A_9))
      | ~ r1_tarski(A_559,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_559),A_9)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_559)) ) ),
    inference(resolution,[status(thm)],[c_18,c_6031])).

tff(c_8543,plain,(
    ! [A_747,A_748] :
      ( r1_tarski(k7_relat_1('#skF_4',A_747),k2_zfmisc_1(A_747,A_748))
      | ~ r1_tarski(A_747,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_747),A_748) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_6041])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_596,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( v1_funct_1(k2_partfun1(A_116,B_117,C_118,D_119))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_601,plain,(
    ! [D_119] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_119))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_596])).

tff(c_609,plain,(
    ! [D_119] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_119)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_601])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_139,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_139])).

tff(c_622,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_657,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_622])).

tff(c_721,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_657])).

tff(c_3153,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3151,c_721])).

tff(c_8558,plain,
    ( ~ r1_tarski('#skF_3','#skF_1')
    | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_8543,c_3153])).

tff(c_8597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3634,c_60,c_8558])).

tff(c_8599,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_8901,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8599,c_8884])).

tff(c_9334,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9330,c_9330,c_8901])).

tff(c_8598,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_9340,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9330,c_8598])).

tff(c_9339,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9330,c_8599])).

tff(c_38,plain,(
    ! [B_24,C_25,A_23] :
      ( k1_xboole_0 = B_24
      | v1_funct_2(C_25,A_23,B_24)
      | k1_relset_1(A_23,B_24,C_25) != A_23
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9410,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_9339,c_38])).

tff(c_9432,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_9340,c_72,c_9410])).

tff(c_9456,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9334,c_9432])).

tff(c_9534,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9528,c_9456])).

tff(c_9562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_9534])).

tff(c_9563,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9578,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_9563,c_6])).

tff(c_9564,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_9570,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_9564])).

tff(c_9588,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9578,c_9570,c_62])).

tff(c_9609,plain,(
    ! [A_872,B_873] :
      ( r1_tarski(A_872,B_873)
      | ~ m1_subset_1(A_872,k1_zfmisc_1(B_873)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9617,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_9588,c_9609])).

tff(c_9579,plain,(
    ! [A_868] : k2_zfmisc_1(A_868,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_9563,c_6])).

tff(c_9583,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9579,c_20])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_9565,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_2])).

tff(c_12374,plain,(
    ! [C_1241,A_1242,B_1243] :
      ( v4_relat_1(C_1241,A_1242)
      | ~ m1_subset_1(C_1241,k1_zfmisc_1(k2_zfmisc_1(A_1242,B_1243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12422,plain,(
    ! [A_1254,A_1255,B_1256] :
      ( v4_relat_1(A_1254,A_1255)
      | ~ r1_tarski(A_1254,k2_zfmisc_1(A_1255,B_1256)) ) ),
    inference(resolution,[status(thm)],[c_12,c_12374])).

tff(c_12438,plain,(
    ! [A_1255] : v4_relat_1('#skF_1',A_1255) ),
    inference(resolution,[status(thm)],[c_9565,c_12422])).

tff(c_12452,plain,(
    ! [B_1261,A_1262] :
      ( k7_relat_1(B_1261,A_1262) = B_1261
      | ~ v4_relat_1(B_1261,A_1262)
      | ~ v1_relat_1(B_1261) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12455,plain,(
    ! [A_1255] :
      ( k7_relat_1('#skF_1',A_1255) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12438,c_12452])).

tff(c_12467,plain,(
    ! [A_1255] : k7_relat_1('#skF_1',A_1255) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_12455])).

tff(c_12621,plain,(
    ! [B_1283,A_1284] :
      ( k1_relat_1(k7_relat_1(B_1283,A_1284)) = A_1284
      | ~ r1_tarski(A_1284,k1_relat_1(B_1283))
      | ~ v1_relat_1(B_1283) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12655,plain,(
    ! [B_1285] :
      ( k1_relat_1(k7_relat_1(B_1285,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1285) ) ),
    inference(resolution,[status(thm)],[c_9565,c_12621])).

tff(c_12676,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12467,c_12655])).

tff(c_12684,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_12676])).

tff(c_12697,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12684,c_24])).

tff(c_12726,plain,(
    ! [A_1288] :
      ( A_1288 = '#skF_1'
      | ~ r1_tarski(A_1288,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_12684,c_12467,c_12697])).

tff(c_12746,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9617,c_12726])).

tff(c_9571,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9570,c_64])).

tff(c_12780,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12746,c_12746,c_9571])).

tff(c_12749,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_12726])).

tff(c_12794,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12746,c_12749])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_9589,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_9563,c_8])).

tff(c_10659,plain,(
    ! [C_1019,B_1020,A_1021] :
      ( v5_relat_1(C_1019,B_1020)
      | ~ m1_subset_1(C_1019,k1_zfmisc_1(k2_zfmisc_1(A_1021,B_1020))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10683,plain,(
    ! [C_1025,B_1026] :
      ( v5_relat_1(C_1025,B_1026)
      | ~ m1_subset_1(C_1025,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9589,c_10659])).

tff(c_10690,plain,(
    ! [B_1026] : v5_relat_1('#skF_4',B_1026) ),
    inference(resolution,[status(thm)],[c_9588,c_10683])).

tff(c_9618,plain,(
    ! [B_874,A_875] :
      ( v1_relat_1(B_874)
      | ~ m1_subset_1(B_874,k1_zfmisc_1(A_875))
      | ~ v1_relat_1(A_875) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9624,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_9588,c_9618])).

tff(c_9628,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_9624])).

tff(c_10671,plain,(
    ! [C_1022,A_1023,B_1024] :
      ( v4_relat_1(C_1022,A_1023)
      | ~ m1_subset_1(C_1022,k1_zfmisc_1(k2_zfmisc_1(A_1023,B_1024))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10704,plain,(
    ! [C_1032,A_1033] :
      ( v4_relat_1(C_1032,A_1033)
      | ~ m1_subset_1(C_1032,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9578,c_10671])).

tff(c_10712,plain,(
    ! [A_1034] : v4_relat_1('#skF_4',A_1034) ),
    inference(resolution,[status(thm)],[c_9588,c_10704])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10715,plain,(
    ! [A_1034] :
      ( k7_relat_1('#skF_4',A_1034) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10712,c_22])).

tff(c_10718,plain,(
    ! [A_1034] : k7_relat_1('#skF_4',A_1034) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9628,c_10715])).

tff(c_32,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_23,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_69,plain,(
    ! [A_23] :
      ( v1_funct_2(k1_xboole_0,A_23,k1_xboole_0)
      | k1_xboole_0 = A_23
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32])).

tff(c_10731,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_1',A_23,'#skF_1')
      | A_23 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_9563,c_9563,c_9563,c_9563,c_69])).

tff(c_10732,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10731])).

tff(c_10735,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_10732])).

tff(c_10739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9565,c_10735])).

tff(c_10741,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10731])).

tff(c_10681,plain,(
    ! [C_1022,A_2] :
      ( v4_relat_1(C_1022,A_2)
      | ~ m1_subset_1(C_1022,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9578,c_10671])).

tff(c_10759,plain,(
    ! [A_1038] : v4_relat_1('#skF_1',A_1038) ),
    inference(resolution,[status(thm)],[c_10741,c_10681])).

tff(c_10762,plain,(
    ! [A_1038] :
      ( k7_relat_1('#skF_1',A_1038) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10759,c_22])).

tff(c_10765,plain,(
    ! [A_1038] : k7_relat_1('#skF_1',A_1038) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_10762])).

tff(c_10693,plain,(
    ! [B_1030,A_1031] :
      ( k1_relat_1(k7_relat_1(B_1030,A_1031)) = A_1031
      | ~ r1_tarski(A_1031,k1_relat_1(B_1030))
      | ~ v1_relat_1(B_1030) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10787,plain,(
    ! [B_1045] :
      ( k1_relat_1(k7_relat_1(B_1045,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1045) ) ),
    inference(resolution,[status(thm)],[c_9565,c_10693])).

tff(c_10800,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10765,c_10787])).

tff(c_10808,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_10800])).

tff(c_10828,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10808,c_24])).

tff(c_10843,plain,(
    ! [A_1048] :
      ( A_1048 = '#skF_1'
      | ~ r1_tarski(A_1048,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_10808,c_10765,c_10828])).

tff(c_10859,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9617,c_10843])).

tff(c_10896,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10859,c_9565])).

tff(c_11334,plain,(
    ! [A_1101,B_1102,C_1103,D_1104] :
      ( k2_partfun1(A_1101,B_1102,C_1103,D_1104) = k7_relat_1(C_1103,D_1104)
      | ~ m1_subset_1(C_1103,k1_zfmisc_1(k2_zfmisc_1(A_1101,B_1102)))
      | ~ v1_funct_1(C_1103) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12328,plain,(
    ! [A_1237,B_1238,A_1239,D_1240] :
      ( k2_partfun1(A_1237,B_1238,A_1239,D_1240) = k7_relat_1(A_1239,D_1240)
      | ~ v1_funct_1(A_1239)
      | ~ r1_tarski(A_1239,k2_zfmisc_1(A_1237,B_1238)) ) ),
    inference(resolution,[status(thm)],[c_12,c_11334])).

tff(c_12337,plain,(
    ! [A_1237,B_1238,D_1240] :
      ( k2_partfun1(A_1237,B_1238,'#skF_4',D_1240) = k7_relat_1('#skF_4',D_1240)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10896,c_12328])).

tff(c_12344,plain,(
    ! [A_1237,B_1238,D_1240] : k2_partfun1(A_1237,B_1238,'#skF_4',D_1240) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10718,c_12337])).

tff(c_10892,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10859,c_9588])).

tff(c_10891,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10859,c_10859,c_9589])).

tff(c_11487,plain,(
    ! [A_1128,B_1129,C_1130,D_1131] :
      ( m1_subset_1(k2_partfun1(A_1128,B_1129,C_1130,D_1131),k1_zfmisc_1(k2_zfmisc_1(A_1128,B_1129)))
      | ~ m1_subset_1(C_1130,k1_zfmisc_1(k2_zfmisc_1(A_1128,B_1129)))
      | ~ v1_funct_1(C_1130) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_11509,plain,(
    ! [A_1128,B_1129,C_1130,D_1131] :
      ( v1_relat_1(k2_partfun1(A_1128,B_1129,C_1130,D_1131))
      | ~ v1_relat_1(k2_zfmisc_1(A_1128,B_1129))
      | ~ m1_subset_1(C_1130,k1_zfmisc_1(k2_zfmisc_1(A_1128,B_1129)))
      | ~ v1_funct_1(C_1130) ) ),
    inference(resolution,[status(thm)],[c_11487,c_14])).

tff(c_11757,plain,(
    ! [A_1163,B_1164,C_1165,D_1166] :
      ( v1_relat_1(k2_partfun1(A_1163,B_1164,C_1165,D_1166))
      | ~ m1_subset_1(C_1165,k1_zfmisc_1(k2_zfmisc_1(A_1163,B_1164)))
      | ~ v1_funct_1(C_1165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_11509])).

tff(c_11807,plain,(
    ! [B_1175,C_1176,D_1177] :
      ( v1_relat_1(k2_partfun1('#skF_4',B_1175,C_1176,D_1177))
      | ~ m1_subset_1(C_1176,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10891,c_11757])).

tff(c_11811,plain,(
    ! [B_1175,D_1177] :
      ( v1_relat_1(k2_partfun1('#skF_4',B_1175,'#skF_4',D_1177))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10892,c_11807])).

tff(c_11818,plain,(
    ! [B_1175,D_1177] : v1_relat_1(k2_partfun1('#skF_4',B_1175,'#skF_4',D_1177)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_11811])).

tff(c_11117,plain,(
    ! [A_1073,B_1074,C_1075,D_1076] :
      ( v1_funct_1(k2_partfun1(A_1073,B_1074,C_1075,D_1076))
      | ~ m1_subset_1(C_1075,k1_zfmisc_1(k2_zfmisc_1(A_1073,B_1074)))
      | ~ v1_funct_1(C_1075) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_11616,plain,(
    ! [A_1141,B_1142,A_1143,D_1144] :
      ( v1_funct_1(k2_partfun1(A_1141,B_1142,A_1143,D_1144))
      | ~ v1_funct_1(A_1143)
      | ~ r1_tarski(A_1143,k2_zfmisc_1(A_1141,B_1142)) ) ),
    inference(resolution,[status(thm)],[c_12,c_11117])).

tff(c_11623,plain,(
    ! [A_1141,B_1142,D_1144] :
      ( v1_funct_1(k2_partfun1(A_1141,B_1142,'#skF_4',D_1144))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10896,c_11616])).

tff(c_11629,plain,(
    ! [A_1141,B_1142,D_1144] : v1_funct_1(k2_partfun1(A_1141,B_1142,'#skF_4',D_1144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_11623])).

tff(c_10894,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10859,c_10859,c_9578])).

tff(c_11219,plain,(
    ! [B_1086,A_1087] :
      ( m1_subset_1(B_1086,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1086),A_1087)))
      | ~ r1_tarski(k2_relat_1(B_1086),A_1087)
      | ~ v1_funct_1(B_1086)
      | ~ v1_relat_1(B_1086) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_11635,plain,(
    ! [B_1154] :
      ( m1_subset_1(B_1154,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_1154),'#skF_4')
      | ~ v1_funct_1(B_1154)
      | ~ v1_relat_1(B_1154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10894,c_11219])).

tff(c_11646,plain,(
    ! [B_1155] :
      ( m1_subset_1(B_1155,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(B_1155)
      | ~ v5_relat_1(B_1155,'#skF_4')
      | ~ v1_relat_1(B_1155) ) ),
    inference(resolution,[status(thm)],[c_18,c_11635])).

tff(c_10862,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_10843])).

tff(c_9744,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_1',A_23,'#skF_1')
      | A_23 = '#skF_1'
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9563,c_9563,c_9563,c_9563,c_9563,c_69])).

tff(c_9745,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_9744])).

tff(c_9748,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_9745])).

tff(c_9752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9565,c_9748])).

tff(c_9754,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_9744])).

tff(c_9684,plain,(
    ! [C_889,A_890,B_891] :
      ( v4_relat_1(C_889,A_890)
      | ~ m1_subset_1(C_889,k1_zfmisc_1(k2_zfmisc_1(A_890,B_891))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_9694,plain,(
    ! [C_889,A_2] :
      ( v4_relat_1(C_889,A_2)
      | ~ m1_subset_1(C_889,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9578,c_9684])).

tff(c_9772,plain,(
    ! [A_905] : v4_relat_1('#skF_1',A_905) ),
    inference(resolution,[status(thm)],[c_9754,c_9694])).

tff(c_9775,plain,(
    ! [A_905] :
      ( k7_relat_1('#skF_1',A_905) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_9772,c_22])).

tff(c_9778,plain,(
    ! [A_905] : k7_relat_1('#skF_1',A_905) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_9775])).

tff(c_9706,plain,(
    ! [B_897,A_898] :
      ( k1_relat_1(k7_relat_1(B_897,A_898)) = A_898
      | ~ r1_tarski(A_898,k1_relat_1(B_897))
      | ~ v1_relat_1(B_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9800,plain,(
    ! [B_912] :
      ( k1_relat_1(k7_relat_1(B_912,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_912) ) ),
    inference(resolution,[status(thm)],[c_9565,c_9706])).

tff(c_9813,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9778,c_9800])).

tff(c_9821,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_9813])).

tff(c_9841,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_1',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9821,c_24])).

tff(c_9856,plain,(
    ! [A_915] :
      ( A_915 = '#skF_1'
      | ~ r1_tarski(A_915,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9583,c_9821,c_9778,c_9841])).

tff(c_9872,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9617,c_9856])).

tff(c_9907,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9872,c_9565])).

tff(c_10156,plain,(
    ! [A_944,B_945,C_946,D_947] :
      ( v1_funct_1(k2_partfun1(A_944,B_945,C_946,D_947))
      | ~ m1_subset_1(C_946,k1_zfmisc_1(k2_zfmisc_1(A_944,B_945)))
      | ~ v1_funct_1(C_946) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10623,plain,(
    ! [A_1009,B_1010,A_1011,D_1012] :
      ( v1_funct_1(k2_partfun1(A_1009,B_1010,A_1011,D_1012))
      | ~ v1_funct_1(A_1011)
      | ~ r1_tarski(A_1011,k2_zfmisc_1(A_1009,B_1010)) ) ),
    inference(resolution,[status(thm)],[c_12,c_10156])).

tff(c_10630,plain,(
    ! [A_1009,B_1010,D_1012] :
      ( v1_funct_1(k2_partfun1(A_1009,B_1010,'#skF_4',D_1012))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9907,c_10623])).

tff(c_10636,plain,(
    ! [A_1009,B_1010,D_1012] : v1_funct_1(k2_partfun1(A_1009,B_1010,'#skF_4',D_1012)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10630])).

tff(c_9875,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_9856])).

tff(c_9659,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9570,c_9570,c_9570,c_9578,c_9570,c_9570,c_56])).

tff(c_9660,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_9659])).

tff(c_9876,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9875,c_9660])).

tff(c_10044,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9872,c_9872,c_9872,c_9876])).

tff(c_10640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10636,c_10044])).

tff(c_10641,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_9659])).

tff(c_10648,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10641])).

tff(c_10864,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10862,c_10648])).

tff(c_11183,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10859,c_10859,c_10859,c_10859,c_10864])).

tff(c_11653,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'))
    | ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_11646,c_11183])).

tff(c_11670,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11629,c_11653])).

tff(c_11806,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_11670])).

tff(c_11822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11818,c_11806])).

tff(c_11823,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_11670])).

tff(c_12347,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12344,c_11823])).

tff(c_12354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10690,c_12347])).

tff(c_12356,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_10641])).

tff(c_12366,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_12356,c_10])).

tff(c_12744,plain,(
    k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_12366,c_12726])).

tff(c_12953,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12794,c_12746,c_12746,c_12746,c_12744])).

tff(c_12355,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_10641])).

tff(c_12772,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12746,c_12746,c_12746,c_12355])).

tff(c_13044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12780,c_12953,c_12794,c_12794,c_12772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.87/3.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.87/3.15  
% 8.87/3.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.87/3.15  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.87/3.15  
% 8.87/3.15  %Foreground sorts:
% 8.87/3.15  
% 8.87/3.15  
% 8.87/3.15  %Background operators:
% 8.87/3.15  
% 8.87/3.15  
% 8.87/3.15  %Foreground operators:
% 8.87/3.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.87/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.87/3.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.87/3.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.87/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.87/3.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.87/3.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.87/3.15  tff('#skF_2', type, '#skF_2': $i).
% 8.87/3.15  tff('#skF_3', type, '#skF_3': $i).
% 8.87/3.15  tff('#skF_1', type, '#skF_1': $i).
% 8.87/3.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.87/3.15  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.87/3.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.87/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.87/3.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.87/3.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.87/3.15  tff('#skF_4', type, '#skF_4': $i).
% 8.87/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.87/3.15  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.87/3.15  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.87/3.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.87/3.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.87/3.15  
% 8.87/3.18  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 8.87/3.18  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.87/3.18  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.87/3.18  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.87/3.18  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.87/3.18  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 8.87/3.18  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.87/3.18  tff(f_100, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 8.87/3.18  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.87/3.18  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.87/3.18  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 8.87/3.18  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.87/3.18  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.87/3.18  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.87/3.18  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 8.87/3.18  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.87/3.18  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.87/3.18  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.87/3.18  tff(c_111, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.87/3.18  tff(c_117, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_111])).
% 8.87/3.18  tff(c_121, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_117])).
% 8.87/3.18  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.87/3.18  tff(c_72, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 8.87/3.18  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.87/3.18  tff(c_8884, plain, (![A_781, B_782, C_783]: (k1_relset_1(A_781, B_782, C_783)=k1_relat_1(C_783) | ~m1_subset_1(C_783, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.87/3.18  tff(c_8903, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_8884])).
% 8.87/3.18  tff(c_9461, plain, (![B_859, A_860, C_861]: (k1_xboole_0=B_859 | k1_relset_1(A_860, B_859, C_861)=A_860 | ~v1_funct_2(C_861, A_860, B_859) | ~m1_subset_1(C_861, k1_zfmisc_1(k2_zfmisc_1(A_860, B_859))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.87/3.18  tff(c_9474, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_9461])).
% 8.87/3.18  tff(c_9488, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8903, c_9474])).
% 8.87/3.18  tff(c_9489, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_9488])).
% 8.87/3.18  tff(c_24, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.87/3.18  tff(c_9501, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9489, c_24])).
% 8.87/3.18  tff(c_9528, plain, (![A_864]: (k1_relat_1(k7_relat_1('#skF_4', A_864))=A_864 | ~r1_tarski(A_864, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_9501])).
% 8.87/3.18  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.87/3.18  tff(c_9309, plain, (![A_849, B_850, C_851, D_852]: (k2_partfun1(A_849, B_850, C_851, D_852)=k7_relat_1(C_851, D_852) | ~m1_subset_1(C_851, k1_zfmisc_1(k2_zfmisc_1(A_849, B_850))) | ~v1_funct_1(C_851))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.87/3.18  tff(c_9318, plain, (![D_852]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_852)=k7_relat_1('#skF_4', D_852) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_9309])).
% 8.87/3.18  tff(c_9330, plain, (![D_852]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_852)=k7_relat_1('#skF_4', D_852))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9318])).
% 8.87/3.18  tff(c_3135, plain, (![A_361, B_362, C_363, D_364]: (k2_partfun1(A_361, B_362, C_363, D_364)=k7_relat_1(C_363, D_364) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_361, B_362))) | ~v1_funct_1(C_363))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.87/3.18  tff(c_3142, plain, (![D_364]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_364)=k7_relat_1('#skF_4', D_364) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_3135])).
% 8.87/3.18  tff(c_3151, plain, (![D_364]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_364)=k7_relat_1('#skF_4', D_364))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3142])).
% 8.87/3.18  tff(c_3532, plain, (![A_404, B_405, C_406, D_407]: (m1_subset_1(k2_partfun1(A_404, B_405, C_406, D_407), k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))) | ~v1_funct_1(C_406))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.87/3.18  tff(c_3560, plain, (![D_364]: (m1_subset_1(k7_relat_1('#skF_4', D_364), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3151, c_3532])).
% 8.87/3.18  tff(c_3592, plain, (![D_408]: (m1_subset_1(k7_relat_1('#skF_4', D_408), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_3560])).
% 8.87/3.18  tff(c_26, plain, (![C_19, B_18, A_17]: (v5_relat_1(C_19, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.87/3.18  tff(c_3634, plain, (![D_408]: (v5_relat_1(k7_relat_1('#skF_4', D_408), '#skF_2'))), inference(resolution, [status(thm)], [c_3592, c_26])).
% 8.87/3.18  tff(c_14, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.87/3.18  tff(c_3614, plain, (![D_408]: (v1_relat_1(k7_relat_1('#skF_4', D_408)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_3592, c_14])).
% 8.87/3.18  tff(c_3637, plain, (![D_408]: (v1_relat_1(k7_relat_1('#skF_4', D_408)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3614])).
% 8.87/3.18  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.87/3.18  tff(c_2905, plain, (![A_329, B_330, C_331, D_332]: (v1_funct_1(k2_partfun1(A_329, B_330, C_331, D_332)) | ~m1_subset_1(C_331, k1_zfmisc_1(k2_zfmisc_1(A_329, B_330))) | ~v1_funct_1(C_331))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.87/3.18  tff(c_2910, plain, (![D_332]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_332)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_2905])).
% 8.87/3.18  tff(c_2918, plain, (![D_332]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_332)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2910])).
% 8.87/3.18  tff(c_3152, plain, (![D_332]: (v1_funct_1(k7_relat_1('#skF_4', D_332)))), inference(demodulation, [status(thm), theory('equality')], [c_3151, c_2918])).
% 8.87/3.18  tff(c_936, plain, (![A_170, B_171, C_172]: (k1_relset_1(A_170, B_171, C_172)=k1_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.87/3.18  tff(c_951, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_936])).
% 8.87/3.18  tff(c_3370, plain, (![B_394, A_395, C_396]: (k1_xboole_0=B_394 | k1_relset_1(A_395, B_394, C_396)=A_395 | ~v1_funct_2(C_396, A_395, B_394) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.87/3.18  tff(c_3380, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_3370])).
% 8.87/3.18  tff(c_3391, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_951, c_3380])).
% 8.87/3.18  tff(c_3392, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_3391])).
% 8.87/3.18  tff(c_3408, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3392, c_24])).
% 8.87/3.18  tff(c_3416, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_3408])).
% 8.87/3.18  tff(c_3025, plain, (![B_350, A_351]: (m1_subset_1(B_350, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_350), A_351))) | ~r1_tarski(k2_relat_1(B_350), A_351) | ~v1_funct_1(B_350) | ~v1_relat_1(B_350))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.87/3.18  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.87/3.18  tff(c_4727, plain, (![B_510, A_511]: (r1_tarski(B_510, k2_zfmisc_1(k1_relat_1(B_510), A_511)) | ~r1_tarski(k2_relat_1(B_510), A_511) | ~v1_funct_1(B_510) | ~v1_relat_1(B_510))), inference(resolution, [status(thm)], [c_3025, c_10])).
% 8.87/3.18  tff(c_4782, plain, (![A_15, A_511]: (r1_tarski(k7_relat_1('#skF_4', A_15), k2_zfmisc_1(A_15, A_511)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_15)), A_511) | ~v1_funct_1(k7_relat_1('#skF_4', A_15)) | ~v1_relat_1(k7_relat_1('#skF_4', A_15)) | ~r1_tarski(A_15, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3416, c_4727])).
% 8.87/3.18  tff(c_6031, plain, (![A_559, A_560]: (r1_tarski(k7_relat_1('#skF_4', A_559), k2_zfmisc_1(A_559, A_560)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_559)), A_560) | ~r1_tarski(A_559, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_3152, c_4782])).
% 8.87/3.18  tff(c_6041, plain, (![A_559, A_9]: (r1_tarski(k7_relat_1('#skF_4', A_559), k2_zfmisc_1(A_559, A_9)) | ~r1_tarski(A_559, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_559), A_9) | ~v1_relat_1(k7_relat_1('#skF_4', A_559)))), inference(resolution, [status(thm)], [c_18, c_6031])).
% 8.87/3.18  tff(c_8543, plain, (![A_747, A_748]: (r1_tarski(k7_relat_1('#skF_4', A_747), k2_zfmisc_1(A_747, A_748)) | ~r1_tarski(A_747, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_747), A_748))), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_6041])).
% 8.87/3.18  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.87/3.18  tff(c_596, plain, (![A_116, B_117, C_118, D_119]: (v1_funct_1(k2_partfun1(A_116, B_117, C_118, D_119)) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(C_118))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.87/3.18  tff(c_601, plain, (![D_119]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_119)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_596])).
% 8.87/3.18  tff(c_609, plain, (![D_119]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_119)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_601])).
% 8.87/3.18  tff(c_56, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.87/3.18  tff(c_139, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 8.87/3.18  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_609, c_139])).
% 8.87/3.18  tff(c_622, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 8.87/3.18  tff(c_657, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_622])).
% 8.87/3.18  tff(c_721, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_657])).
% 8.87/3.18  tff(c_3153, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3151, c_721])).
% 8.87/3.18  tff(c_8558, plain, (~r1_tarski('#skF_3', '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_8543, c_3153])).
% 8.87/3.18  tff(c_8597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3634, c_60, c_8558])).
% 8.87/3.18  tff(c_8599, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_622])).
% 8.87/3.18  tff(c_8901, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_8599, c_8884])).
% 8.87/3.18  tff(c_9334, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9330, c_9330, c_8901])).
% 8.87/3.18  tff(c_8598, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_622])).
% 8.87/3.18  tff(c_9340, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9330, c_8598])).
% 8.87/3.18  tff(c_9339, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9330, c_8599])).
% 8.87/3.18  tff(c_38, plain, (![B_24, C_25, A_23]: (k1_xboole_0=B_24 | v1_funct_2(C_25, A_23, B_24) | k1_relset_1(A_23, B_24, C_25)!=A_23 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.87/3.18  tff(c_9410, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_9339, c_38])).
% 8.87/3.18  tff(c_9432, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_9340, c_72, c_9410])).
% 8.87/3.18  tff(c_9456, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9334, c_9432])).
% 8.87/3.18  tff(c_9534, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9528, c_9456])).
% 8.87/3.18  tff(c_9562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_9534])).
% 8.87/3.18  tff(c_9563, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 8.87/3.18  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.87/3.18  tff(c_9578, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_9563, c_6])).
% 8.87/3.18  tff(c_9564, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 8.87/3.18  tff(c_9570, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_9564])).
% 8.87/3.18  tff(c_9588, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9578, c_9570, c_62])).
% 8.87/3.18  tff(c_9609, plain, (![A_872, B_873]: (r1_tarski(A_872, B_873) | ~m1_subset_1(A_872, k1_zfmisc_1(B_873)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.87/3.18  tff(c_9617, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_9588, c_9609])).
% 8.87/3.18  tff(c_9579, plain, (![A_868]: (k2_zfmisc_1(A_868, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_9563, c_6])).
% 8.87/3.18  tff(c_9583, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9579, c_20])).
% 8.87/3.18  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.87/3.18  tff(c_9565, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_2])).
% 8.87/3.18  tff(c_12374, plain, (![C_1241, A_1242, B_1243]: (v4_relat_1(C_1241, A_1242) | ~m1_subset_1(C_1241, k1_zfmisc_1(k2_zfmisc_1(A_1242, B_1243))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.87/3.18  tff(c_12422, plain, (![A_1254, A_1255, B_1256]: (v4_relat_1(A_1254, A_1255) | ~r1_tarski(A_1254, k2_zfmisc_1(A_1255, B_1256)))), inference(resolution, [status(thm)], [c_12, c_12374])).
% 8.87/3.18  tff(c_12438, plain, (![A_1255]: (v4_relat_1('#skF_1', A_1255))), inference(resolution, [status(thm)], [c_9565, c_12422])).
% 8.87/3.18  tff(c_12452, plain, (![B_1261, A_1262]: (k7_relat_1(B_1261, A_1262)=B_1261 | ~v4_relat_1(B_1261, A_1262) | ~v1_relat_1(B_1261))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.87/3.18  tff(c_12455, plain, (![A_1255]: (k7_relat_1('#skF_1', A_1255)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_12438, c_12452])).
% 8.87/3.18  tff(c_12467, plain, (![A_1255]: (k7_relat_1('#skF_1', A_1255)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_12455])).
% 8.87/3.18  tff(c_12621, plain, (![B_1283, A_1284]: (k1_relat_1(k7_relat_1(B_1283, A_1284))=A_1284 | ~r1_tarski(A_1284, k1_relat_1(B_1283)) | ~v1_relat_1(B_1283))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.87/3.18  tff(c_12655, plain, (![B_1285]: (k1_relat_1(k7_relat_1(B_1285, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1285))), inference(resolution, [status(thm)], [c_9565, c_12621])).
% 8.87/3.18  tff(c_12676, plain, (k1_relat_1('#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12467, c_12655])).
% 8.87/3.18  tff(c_12684, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_12676])).
% 8.87/3.18  tff(c_12697, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_1', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12684, c_24])).
% 8.87/3.18  tff(c_12726, plain, (![A_1288]: (A_1288='#skF_1' | ~r1_tarski(A_1288, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_12684, c_12467, c_12697])).
% 8.87/3.18  tff(c_12746, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_9617, c_12726])).
% 8.87/3.18  tff(c_9571, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9570, c_64])).
% 8.87/3.18  tff(c_12780, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12746, c_12746, c_9571])).
% 8.87/3.18  tff(c_12749, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_12726])).
% 8.87/3.18  tff(c_12794, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12746, c_12749])).
% 8.87/3.18  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.87/3.18  tff(c_9589, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_9563, c_8])).
% 8.87/3.18  tff(c_10659, plain, (![C_1019, B_1020, A_1021]: (v5_relat_1(C_1019, B_1020) | ~m1_subset_1(C_1019, k1_zfmisc_1(k2_zfmisc_1(A_1021, B_1020))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.87/3.18  tff(c_10683, plain, (![C_1025, B_1026]: (v5_relat_1(C_1025, B_1026) | ~m1_subset_1(C_1025, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9589, c_10659])).
% 8.87/3.18  tff(c_10690, plain, (![B_1026]: (v5_relat_1('#skF_4', B_1026))), inference(resolution, [status(thm)], [c_9588, c_10683])).
% 8.87/3.18  tff(c_9618, plain, (![B_874, A_875]: (v1_relat_1(B_874) | ~m1_subset_1(B_874, k1_zfmisc_1(A_875)) | ~v1_relat_1(A_875))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.87/3.18  tff(c_9624, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_9588, c_9618])).
% 8.87/3.18  tff(c_9628, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_9624])).
% 8.87/3.18  tff(c_10671, plain, (![C_1022, A_1023, B_1024]: (v4_relat_1(C_1022, A_1023) | ~m1_subset_1(C_1022, k1_zfmisc_1(k2_zfmisc_1(A_1023, B_1024))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.87/3.18  tff(c_10704, plain, (![C_1032, A_1033]: (v4_relat_1(C_1032, A_1033) | ~m1_subset_1(C_1032, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9578, c_10671])).
% 8.87/3.18  tff(c_10712, plain, (![A_1034]: (v4_relat_1('#skF_4', A_1034))), inference(resolution, [status(thm)], [c_9588, c_10704])).
% 8.87/3.18  tff(c_22, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.87/3.18  tff(c_10715, plain, (![A_1034]: (k7_relat_1('#skF_4', A_1034)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10712, c_22])).
% 8.87/3.18  tff(c_10718, plain, (![A_1034]: (k7_relat_1('#skF_4', A_1034)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9628, c_10715])).
% 8.87/3.18  tff(c_32, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_23, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.87/3.18  tff(c_69, plain, (![A_23]: (v1_funct_2(k1_xboole_0, A_23, k1_xboole_0) | k1_xboole_0=A_23 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32])).
% 8.87/3.18  tff(c_10731, plain, (![A_23]: (v1_funct_2('#skF_1', A_23, '#skF_1') | A_23='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_9563, c_9563, c_9563, c_9563, c_69])).
% 8.87/3.18  tff(c_10732, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_10731])).
% 8.87/3.18  tff(c_10735, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_12, c_10732])).
% 8.87/3.18  tff(c_10739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9565, c_10735])).
% 8.87/3.18  tff(c_10741, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_10731])).
% 8.87/3.18  tff(c_10681, plain, (![C_1022, A_2]: (v4_relat_1(C_1022, A_2) | ~m1_subset_1(C_1022, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9578, c_10671])).
% 8.87/3.18  tff(c_10759, plain, (![A_1038]: (v4_relat_1('#skF_1', A_1038))), inference(resolution, [status(thm)], [c_10741, c_10681])).
% 8.87/3.18  tff(c_10762, plain, (![A_1038]: (k7_relat_1('#skF_1', A_1038)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_10759, c_22])).
% 8.87/3.18  tff(c_10765, plain, (![A_1038]: (k7_relat_1('#skF_1', A_1038)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_10762])).
% 8.87/3.18  tff(c_10693, plain, (![B_1030, A_1031]: (k1_relat_1(k7_relat_1(B_1030, A_1031))=A_1031 | ~r1_tarski(A_1031, k1_relat_1(B_1030)) | ~v1_relat_1(B_1030))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.87/3.18  tff(c_10787, plain, (![B_1045]: (k1_relat_1(k7_relat_1(B_1045, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1045))), inference(resolution, [status(thm)], [c_9565, c_10693])).
% 8.87/3.18  tff(c_10800, plain, (k1_relat_1('#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10765, c_10787])).
% 8.87/3.18  tff(c_10808, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_10800])).
% 8.87/3.18  tff(c_10828, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_1', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10808, c_24])).
% 8.87/3.18  tff(c_10843, plain, (![A_1048]: (A_1048='#skF_1' | ~r1_tarski(A_1048, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_10808, c_10765, c_10828])).
% 8.87/3.18  tff(c_10859, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_9617, c_10843])).
% 8.87/3.18  tff(c_10896, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_10859, c_9565])).
% 8.87/3.18  tff(c_11334, plain, (![A_1101, B_1102, C_1103, D_1104]: (k2_partfun1(A_1101, B_1102, C_1103, D_1104)=k7_relat_1(C_1103, D_1104) | ~m1_subset_1(C_1103, k1_zfmisc_1(k2_zfmisc_1(A_1101, B_1102))) | ~v1_funct_1(C_1103))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.87/3.18  tff(c_12328, plain, (![A_1237, B_1238, A_1239, D_1240]: (k2_partfun1(A_1237, B_1238, A_1239, D_1240)=k7_relat_1(A_1239, D_1240) | ~v1_funct_1(A_1239) | ~r1_tarski(A_1239, k2_zfmisc_1(A_1237, B_1238)))), inference(resolution, [status(thm)], [c_12, c_11334])).
% 8.87/3.18  tff(c_12337, plain, (![A_1237, B_1238, D_1240]: (k2_partfun1(A_1237, B_1238, '#skF_4', D_1240)=k7_relat_1('#skF_4', D_1240) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10896, c_12328])).
% 8.87/3.18  tff(c_12344, plain, (![A_1237, B_1238, D_1240]: (k2_partfun1(A_1237, B_1238, '#skF_4', D_1240)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10718, c_12337])).
% 8.87/3.18  tff(c_10892, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10859, c_9588])).
% 8.87/3.18  tff(c_10891, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10859, c_10859, c_9589])).
% 8.87/3.18  tff(c_11487, plain, (![A_1128, B_1129, C_1130, D_1131]: (m1_subset_1(k2_partfun1(A_1128, B_1129, C_1130, D_1131), k1_zfmisc_1(k2_zfmisc_1(A_1128, B_1129))) | ~m1_subset_1(C_1130, k1_zfmisc_1(k2_zfmisc_1(A_1128, B_1129))) | ~v1_funct_1(C_1130))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.87/3.18  tff(c_11509, plain, (![A_1128, B_1129, C_1130, D_1131]: (v1_relat_1(k2_partfun1(A_1128, B_1129, C_1130, D_1131)) | ~v1_relat_1(k2_zfmisc_1(A_1128, B_1129)) | ~m1_subset_1(C_1130, k1_zfmisc_1(k2_zfmisc_1(A_1128, B_1129))) | ~v1_funct_1(C_1130))), inference(resolution, [status(thm)], [c_11487, c_14])).
% 8.87/3.18  tff(c_11757, plain, (![A_1163, B_1164, C_1165, D_1166]: (v1_relat_1(k2_partfun1(A_1163, B_1164, C_1165, D_1166)) | ~m1_subset_1(C_1165, k1_zfmisc_1(k2_zfmisc_1(A_1163, B_1164))) | ~v1_funct_1(C_1165))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_11509])).
% 8.87/3.18  tff(c_11807, plain, (![B_1175, C_1176, D_1177]: (v1_relat_1(k2_partfun1('#skF_4', B_1175, C_1176, D_1177)) | ~m1_subset_1(C_1176, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1176))), inference(superposition, [status(thm), theory('equality')], [c_10891, c_11757])).
% 8.87/3.18  tff(c_11811, plain, (![B_1175, D_1177]: (v1_relat_1(k2_partfun1('#skF_4', B_1175, '#skF_4', D_1177)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10892, c_11807])).
% 8.87/3.18  tff(c_11818, plain, (![B_1175, D_1177]: (v1_relat_1(k2_partfun1('#skF_4', B_1175, '#skF_4', D_1177)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_11811])).
% 8.87/3.18  tff(c_11117, plain, (![A_1073, B_1074, C_1075, D_1076]: (v1_funct_1(k2_partfun1(A_1073, B_1074, C_1075, D_1076)) | ~m1_subset_1(C_1075, k1_zfmisc_1(k2_zfmisc_1(A_1073, B_1074))) | ~v1_funct_1(C_1075))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.87/3.18  tff(c_11616, plain, (![A_1141, B_1142, A_1143, D_1144]: (v1_funct_1(k2_partfun1(A_1141, B_1142, A_1143, D_1144)) | ~v1_funct_1(A_1143) | ~r1_tarski(A_1143, k2_zfmisc_1(A_1141, B_1142)))), inference(resolution, [status(thm)], [c_12, c_11117])).
% 8.87/3.18  tff(c_11623, plain, (![A_1141, B_1142, D_1144]: (v1_funct_1(k2_partfun1(A_1141, B_1142, '#skF_4', D_1144)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10896, c_11616])).
% 8.87/3.18  tff(c_11629, plain, (![A_1141, B_1142, D_1144]: (v1_funct_1(k2_partfun1(A_1141, B_1142, '#skF_4', D_1144)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_11623])).
% 8.87/3.18  tff(c_10894, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10859, c_10859, c_9578])).
% 8.87/3.18  tff(c_11219, plain, (![B_1086, A_1087]: (m1_subset_1(B_1086, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_1086), A_1087))) | ~r1_tarski(k2_relat_1(B_1086), A_1087) | ~v1_funct_1(B_1086) | ~v1_relat_1(B_1086))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.87/3.18  tff(c_11635, plain, (![B_1154]: (m1_subset_1(B_1154, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_1154), '#skF_4') | ~v1_funct_1(B_1154) | ~v1_relat_1(B_1154))), inference(superposition, [status(thm), theory('equality')], [c_10894, c_11219])).
% 8.87/3.18  tff(c_11646, plain, (![B_1155]: (m1_subset_1(B_1155, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(B_1155) | ~v5_relat_1(B_1155, '#skF_4') | ~v1_relat_1(B_1155))), inference(resolution, [status(thm)], [c_18, c_11635])).
% 8.87/3.18  tff(c_10862, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_10843])).
% 8.87/3.18  tff(c_9744, plain, (![A_23]: (v1_funct_2('#skF_1', A_23, '#skF_1') | A_23='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9563, c_9563, c_9563, c_9563, c_9563, c_69])).
% 8.87/3.18  tff(c_9745, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_9744])).
% 8.87/3.18  tff(c_9748, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_12, c_9745])).
% 8.87/3.18  tff(c_9752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9565, c_9748])).
% 8.87/3.18  tff(c_9754, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_9744])).
% 8.87/3.18  tff(c_9684, plain, (![C_889, A_890, B_891]: (v4_relat_1(C_889, A_890) | ~m1_subset_1(C_889, k1_zfmisc_1(k2_zfmisc_1(A_890, B_891))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.87/3.18  tff(c_9694, plain, (![C_889, A_2]: (v4_relat_1(C_889, A_2) | ~m1_subset_1(C_889, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9578, c_9684])).
% 8.87/3.18  tff(c_9772, plain, (![A_905]: (v4_relat_1('#skF_1', A_905))), inference(resolution, [status(thm)], [c_9754, c_9694])).
% 8.87/3.18  tff(c_9775, plain, (![A_905]: (k7_relat_1('#skF_1', A_905)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_9772, c_22])).
% 8.87/3.18  tff(c_9778, plain, (![A_905]: (k7_relat_1('#skF_1', A_905)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_9775])).
% 8.87/3.18  tff(c_9706, plain, (![B_897, A_898]: (k1_relat_1(k7_relat_1(B_897, A_898))=A_898 | ~r1_tarski(A_898, k1_relat_1(B_897)) | ~v1_relat_1(B_897))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.87/3.18  tff(c_9800, plain, (![B_912]: (k1_relat_1(k7_relat_1(B_912, '#skF_1'))='#skF_1' | ~v1_relat_1(B_912))), inference(resolution, [status(thm)], [c_9565, c_9706])).
% 8.87/3.18  tff(c_9813, plain, (k1_relat_1('#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9778, c_9800])).
% 8.87/3.18  tff(c_9821, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_9813])).
% 8.87/3.18  tff(c_9841, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_1', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_9821, c_24])).
% 8.87/3.18  tff(c_9856, plain, (![A_915]: (A_915='#skF_1' | ~r1_tarski(A_915, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9583, c_9821, c_9778, c_9841])).
% 8.87/3.18  tff(c_9872, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_9617, c_9856])).
% 8.87/3.18  tff(c_9907, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_9872, c_9565])).
% 8.87/3.18  tff(c_10156, plain, (![A_944, B_945, C_946, D_947]: (v1_funct_1(k2_partfun1(A_944, B_945, C_946, D_947)) | ~m1_subset_1(C_946, k1_zfmisc_1(k2_zfmisc_1(A_944, B_945))) | ~v1_funct_1(C_946))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.87/3.18  tff(c_10623, plain, (![A_1009, B_1010, A_1011, D_1012]: (v1_funct_1(k2_partfun1(A_1009, B_1010, A_1011, D_1012)) | ~v1_funct_1(A_1011) | ~r1_tarski(A_1011, k2_zfmisc_1(A_1009, B_1010)))), inference(resolution, [status(thm)], [c_12, c_10156])).
% 8.87/3.18  tff(c_10630, plain, (![A_1009, B_1010, D_1012]: (v1_funct_1(k2_partfun1(A_1009, B_1010, '#skF_4', D_1012)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_9907, c_10623])).
% 8.87/3.18  tff(c_10636, plain, (![A_1009, B_1010, D_1012]: (v1_funct_1(k2_partfun1(A_1009, B_1010, '#skF_4', D_1012)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_10630])).
% 8.87/3.18  tff(c_9875, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_9856])).
% 8.87/3.18  tff(c_9659, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9570, c_9570, c_9570, c_9578, c_9570, c_9570, c_56])).
% 8.87/3.18  tff(c_9660, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_9659])).
% 8.87/3.18  tff(c_9876, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9875, c_9660])).
% 8.87/3.18  tff(c_10044, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9872, c_9872, c_9872, c_9876])).
% 8.87/3.18  tff(c_10640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10636, c_10044])).
% 8.87/3.18  tff(c_10641, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_9659])).
% 8.87/3.18  tff(c_10648, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_10641])).
% 8.87/3.18  tff(c_10864, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10862, c_10648])).
% 8.87/3.18  tff(c_11183, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10859, c_10859, c_10859, c_10859, c_10864])).
% 8.87/3.18  tff(c_11653, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')) | ~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_11646, c_11183])).
% 8.87/3.18  tff(c_11670, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11629, c_11653])).
% 8.87/3.18  tff(c_11806, plain, (~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_11670])).
% 8.87/3.18  tff(c_11822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11818, c_11806])).
% 8.87/3.18  tff(c_11823, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_11670])).
% 8.87/3.18  tff(c_12347, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12344, c_11823])).
% 8.87/3.18  tff(c_12354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10690, c_12347])).
% 8.87/3.18  tff(c_12356, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_10641])).
% 8.87/3.18  tff(c_12366, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_12356, c_10])).
% 8.87/3.18  tff(c_12744, plain, (k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_12366, c_12726])).
% 8.87/3.18  tff(c_12953, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12794, c_12746, c_12746, c_12746, c_12744])).
% 8.87/3.18  tff(c_12355, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_10641])).
% 8.87/3.18  tff(c_12772, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12746, c_12746, c_12746, c_12355])).
% 8.87/3.18  tff(c_13044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12780, c_12953, c_12794, c_12794, c_12772])).
% 8.87/3.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.87/3.18  
% 8.87/3.18  Inference rules
% 8.87/3.18  ----------------------
% 8.87/3.18  #Ref     : 0
% 8.87/3.18  #Sup     : 2811
% 8.87/3.18  #Fact    : 0
% 8.87/3.18  #Define  : 0
% 8.87/3.18  #Split   : 40
% 8.87/3.18  #Chain   : 0
% 8.87/3.18  #Close   : 0
% 8.87/3.18  
% 8.87/3.18  Ordering : KBO
% 8.87/3.18  
% 8.87/3.18  Simplification rules
% 8.87/3.18  ----------------------
% 8.87/3.18  #Subsume      : 632
% 8.87/3.18  #Demod        : 2861
% 8.87/3.18  #Tautology    : 1240
% 8.87/3.18  #SimpNegUnit  : 147
% 8.87/3.19  #BackRed      : 214
% 8.87/3.19  
% 8.87/3.19  #Partial instantiations: 0
% 8.87/3.19  #Strategies tried      : 1
% 8.87/3.19  
% 8.87/3.19  Timing (in seconds)
% 8.87/3.19  ----------------------
% 8.87/3.19  Preprocessing        : 0.34
% 8.87/3.19  Parsing              : 0.18
% 9.24/3.19  CNF conversion       : 0.02
% 9.24/3.19  Main loop            : 2.03
% 9.24/3.19  Inferencing          : 0.70
% 9.24/3.19  Reduction            : 0.73
% 9.24/3.19  Demodulation         : 0.53
% 9.24/3.19  BG Simplification    : 0.06
% 9.24/3.19  Subsumption          : 0.37
% 9.24/3.19  Abstraction          : 0.08
% 9.24/3.19  MUC search           : 0.00
% 9.24/3.19  Cooper               : 0.00
% 9.24/3.19  Total                : 2.45
% 9.24/3.19  Index Insertion      : 0.00
% 9.24/3.19  Index Deletion       : 0.00
% 9.24/3.19  Index Matching       : 0.00
% 9.24/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
