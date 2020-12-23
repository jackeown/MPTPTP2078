%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:18 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 272 expanded)
%              Number of leaves         :   48 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 ( 583 expanded)
%              Number of equality atoms :   49 ( 227 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_8 > #skF_9 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
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

tff(f_144,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_155,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_134,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1489,plain,(
    ! [A_200,B_201,C_202] :
      ( k2_relset_1(A_200,B_201,C_202) = k2_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1513,plain,(
    k2_relset_1('#skF_9','#skF_10','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_134,c_1489])).

tff(c_1596,plain,(
    ! [A_215,B_216,C_217] :
      ( m1_subset_1(k2_relset_1(A_215,B_216,C_217),k1_zfmisc_1(B_216))
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1626,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10'))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1513,c_1596])).

tff(c_1640,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_1626])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1690,plain,(
    r1_tarski(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_1640,c_26])).

tff(c_227,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_240,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_134,c_227])).

tff(c_138,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_132,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_146,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_136,plain,(
    v1_funct_2('#skF_11','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1526,plain,(
    ! [A_205,B_206,C_207] :
      ( k1_relset_1(A_205,B_206,C_207) = k1_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1550,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_134,c_1526])).

tff(c_2996,plain,(
    ! [B_351,A_352,C_353] :
      ( k1_xboole_0 = B_351
      | k1_relset_1(A_352,B_351,C_353) = A_352
      | ~ v1_funct_2(C_353,A_352,B_351)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_352,B_351))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3026,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_relset_1('#skF_9','#skF_10','#skF_11') = '#skF_9'
    | ~ v1_funct_2('#skF_11','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_134,c_2996])).

tff(c_3040,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_relat_1('#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_1550,c_3026])).

tff(c_3041,plain,(
    k1_relat_1('#skF_11') = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_3040])).

tff(c_78,plain,(
    ! [E_64,B_46] :
      ( r2_hidden(E_64,k1_funct_2(k1_relat_1(E_64),B_46))
      | ~ r1_tarski(k2_relat_1(E_64),B_46)
      | ~ v1_funct_1(E_64)
      | ~ v1_relat_1(E_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3050,plain,(
    ! [B_46] :
      ( r2_hidden('#skF_11',k1_funct_2('#skF_9',B_46))
      | ~ r1_tarski(k2_relat_1('#skF_11'),B_46)
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3041,c_78])).

tff(c_3358,plain,(
    ! [B_366] :
      ( r2_hidden('#skF_11',k1_funct_2('#skF_9',B_366))
      | ~ r1_tarski(k2_relat_1('#skF_11'),B_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_138,c_3050])).

tff(c_130,plain,(
    ~ r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_3368,plain,(
    ~ r1_tarski(k2_relat_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_3358,c_130])).

tff(c_3375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_3368])).

tff(c_3376,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_22,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3393,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3376,c_3376,c_22])).

tff(c_3401,plain,(
    ! [A_372,B_373] : v1_relat_1(k2_zfmisc_1(A_372,B_373)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3403,plain,(
    v1_relat_1('#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_3393,c_3401])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3378,plain,(
    ! [A_12] : r1_tarski('#skF_9',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3376,c_18])).

tff(c_3377,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_3383,plain,(
    '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3376,c_3377])).

tff(c_3443,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3393,c_3383,c_134])).

tff(c_3472,plain,(
    ! [A_395,B_396] :
      ( r1_tarski(A_395,B_396)
      | ~ m1_subset_1(A_395,k1_zfmisc_1(B_396)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3480,plain,(
    r1_tarski('#skF_11','#skF_9') ),
    inference(resolution,[status(thm)],[c_3443,c_3472])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3495,plain,
    ( '#skF_11' = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(resolution,[status(thm)],[c_3480,c_12])).

tff(c_3498,plain,(
    '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3378,c_3495])).

tff(c_3503,plain,(
    v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3498,c_138])).

tff(c_120,plain,(
    ! [A_65,B_66] : v1_xboole_0('#skF_8'(A_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3568,plain,(
    ! [A_404,B_405] :
      ( r2_hidden('#skF_2'(A_404,B_405),A_404)
      | r1_tarski(A_404,B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3573,plain,(
    ! [A_406,B_407] :
      ( ~ v1_xboole_0(A_406)
      | r1_tarski(A_406,B_407) ) ),
    inference(resolution,[status(thm)],[c_3568,c_2])).

tff(c_3481,plain,(
    ! [B_397,A_398] :
      ( B_397 = A_398
      | ~ r1_tarski(B_397,A_398)
      | ~ r1_tarski(A_398,B_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3489,plain,(
    ! [A_12] :
      ( A_12 = '#skF_9'
      | ~ r1_tarski(A_12,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3378,c_3481])).

tff(c_3582,plain,(
    ! [A_408] :
      ( A_408 = '#skF_9'
      | ~ v1_xboole_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_3573,c_3489])).

tff(c_3586,plain,(
    ! [A_65,B_66] : '#skF_8'(A_65,B_66) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_120,c_3582])).

tff(c_114,plain,(
    ! [A_65,B_66] : v5_relat_1('#skF_8'(A_65,B_66),B_66) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3599,plain,(
    ! [B_66] : v5_relat_1('#skF_9',B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3586,c_114])).

tff(c_3936,plain,(
    ! [B_450,A_451] :
      ( r1_tarski(k2_relat_1(B_450),A_451)
      | ~ v5_relat_1(B_450,A_451)
      | ~ v1_relat_1(B_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4113,plain,(
    ! [B_466] :
      ( k2_relat_1(B_466) = '#skF_9'
      | ~ v5_relat_1(B_466,'#skF_9')
      | ~ v1_relat_1(B_466) ) ),
    inference(resolution,[status(thm)],[c_3936,c_3489])).

tff(c_4129,plain,
    ( k2_relat_1('#skF_9') = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3599,c_4113])).

tff(c_4141,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3403,c_4129])).

tff(c_116,plain,(
    ! [A_65,B_66] : v4_relat_1('#skF_8'(A_65,B_66),A_65) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3600,plain,(
    ! [A_65] : v4_relat_1('#skF_9',A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3586,c_116])).

tff(c_3774,plain,(
    ! [B_437,A_438] :
      ( r1_tarski(k1_relat_1(B_437),A_438)
      | ~ v4_relat_1(B_437,A_438)
      | ~ v1_relat_1(B_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3836,plain,(
    ! [B_440] :
      ( k1_relat_1(B_440) = '#skF_9'
      | ~ v4_relat_1(B_440,'#skF_9')
      | ~ v1_relat_1(B_440) ) ),
    inference(resolution,[status(thm)],[c_3774,c_3489])).

tff(c_3840,plain,
    ( k1_relat_1('#skF_9') = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_3600,c_3836])).

tff(c_3843,plain,(
    k1_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3403,c_3840])).

tff(c_5191,plain,(
    ! [E_559,B_560] :
      ( r2_hidden(E_559,k1_funct_2(k1_relat_1(E_559),B_560))
      | ~ r1_tarski(k2_relat_1(E_559),B_560)
      | ~ v1_funct_1(E_559)
      | ~ v1_relat_1(E_559) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5201,plain,(
    ! [B_560] :
      ( r2_hidden('#skF_9',k1_funct_2('#skF_9',B_560))
      | ~ r1_tarski(k2_relat_1('#skF_9'),B_560)
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3843,c_5191])).

tff(c_5209,plain,(
    ! [B_560] : r2_hidden('#skF_9',k1_funct_2('#skF_9',B_560)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3403,c_3503,c_3378,c_4141,c_5201])).

tff(c_3404,plain,(
    ~ r2_hidden('#skF_11',k1_funct_2('#skF_9','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_130])).

tff(c_3501,plain,(
    ~ r2_hidden('#skF_9',k1_funct_2('#skF_9','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3498,c_3404])).

tff(c_5212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5209,c_3501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:53:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.11  
% 5.81/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.81/2.11  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_4 > #skF_3 > #skF_10 > #skF_5 > #skF_7 > #skF_8 > #skF_9 > #skF_2
% 5.81/2.11  
% 5.81/2.11  %Foreground sorts:
% 5.81/2.11  
% 5.81/2.11  
% 5.81/2.11  %Background operators:
% 5.81/2.11  
% 5.81/2.11  
% 5.81/2.11  %Foreground operators:
% 5.81/2.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.81/2.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.81/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.81/2.11  tff('#skF_11', type, '#skF_11': $i).
% 5.81/2.11  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.81/2.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.81/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.81/2.11  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.81/2.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.81/2.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.81/2.11  tff('#skF_10', type, '#skF_10': $i).
% 5.81/2.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.81/2.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.81/2.11  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.81/2.11  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 5.81/2.11  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.81/2.11  tff('#skF_9', type, '#skF_9': $i).
% 5.81/2.11  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.81/2.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.81/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.81/2.11  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 5.81/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.81/2.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.81/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.81/2.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.81/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.81/2.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.81/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.81/2.11  
% 5.89/2.13  tff(f_178, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_funct_2)).
% 5.89/2.13  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.89/2.13  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.89/2.13  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.89/2.13  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.89/2.13  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.89/2.13  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.89/2.13  tff(f_144, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_funct_2)).
% 5.89/2.13  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.89/2.13  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.89/2.13  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.89/2.13  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.89/2.13  tff(f_155, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 5.89/2.13  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.89/2.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.89/2.13  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.89/2.13  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.89/2.13  tff(c_134, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.89/2.13  tff(c_1489, plain, (![A_200, B_201, C_202]: (k2_relset_1(A_200, B_201, C_202)=k2_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.89/2.13  tff(c_1513, plain, (k2_relset_1('#skF_9', '#skF_10', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_134, c_1489])).
% 5.89/2.13  tff(c_1596, plain, (![A_215, B_216, C_217]: (m1_subset_1(k2_relset_1(A_215, B_216, C_217), k1_zfmisc_1(B_216)) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.89/2.13  tff(c_1626, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10')) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_1513, c_1596])).
% 5.89/2.13  tff(c_1640, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_1626])).
% 5.89/2.13  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.13  tff(c_1690, plain, (r1_tarski(k2_relat_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_1640, c_26])).
% 5.89/2.13  tff(c_227, plain, (![C_100, A_101, B_102]: (v1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.89/2.13  tff(c_240, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_134, c_227])).
% 5.89/2.13  tff(c_138, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.89/2.13  tff(c_132, plain, (k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.89/2.13  tff(c_146, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_132])).
% 5.89/2.13  tff(c_136, plain, (v1_funct_2('#skF_11', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.89/2.13  tff(c_1526, plain, (![A_205, B_206, C_207]: (k1_relset_1(A_205, B_206, C_207)=k1_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.89/2.13  tff(c_1550, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_134, c_1526])).
% 5.89/2.13  tff(c_2996, plain, (![B_351, A_352, C_353]: (k1_xboole_0=B_351 | k1_relset_1(A_352, B_351, C_353)=A_352 | ~v1_funct_2(C_353, A_352, B_351) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_352, B_351))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.89/2.13  tff(c_3026, plain, (k1_xboole_0='#skF_10' | k1_relset_1('#skF_9', '#skF_10', '#skF_11')='#skF_9' | ~v1_funct_2('#skF_11', '#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_134, c_2996])).
% 5.89/2.13  tff(c_3040, plain, (k1_xboole_0='#skF_10' | k1_relat_1('#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_1550, c_3026])).
% 5.89/2.13  tff(c_3041, plain, (k1_relat_1('#skF_11')='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_146, c_3040])).
% 5.89/2.13  tff(c_78, plain, (![E_64, B_46]: (r2_hidden(E_64, k1_funct_2(k1_relat_1(E_64), B_46)) | ~r1_tarski(k2_relat_1(E_64), B_46) | ~v1_funct_1(E_64) | ~v1_relat_1(E_64))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.89/2.13  tff(c_3050, plain, (![B_46]: (r2_hidden('#skF_11', k1_funct_2('#skF_9', B_46)) | ~r1_tarski(k2_relat_1('#skF_11'), B_46) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_3041, c_78])).
% 5.89/2.13  tff(c_3358, plain, (![B_366]: (r2_hidden('#skF_11', k1_funct_2('#skF_9', B_366)) | ~r1_tarski(k2_relat_1('#skF_11'), B_366))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_138, c_3050])).
% 5.89/2.13  tff(c_130, plain, (~r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.89/2.13  tff(c_3368, plain, (~r1_tarski(k2_relat_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_3358, c_130])).
% 5.89/2.13  tff(c_3375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1690, c_3368])).
% 5.89/2.13  tff(c_3376, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_132])).
% 5.89/2.13  tff(c_22, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.89/2.13  tff(c_3393, plain, (![A_13]: (k2_zfmisc_1(A_13, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3376, c_3376, c_22])).
% 5.89/2.13  tff(c_3401, plain, (![A_372, B_373]: (v1_relat_1(k2_zfmisc_1(A_372, B_373)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.89/2.13  tff(c_3403, plain, (v1_relat_1('#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_3393, c_3401])).
% 5.89/2.13  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.89/2.13  tff(c_3378, plain, (![A_12]: (r1_tarski('#skF_9', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_3376, c_18])).
% 5.89/2.13  tff(c_3377, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_132])).
% 5.89/2.13  tff(c_3383, plain, ('#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3376, c_3377])).
% 5.89/2.13  tff(c_3443, plain, (m1_subset_1('#skF_11', k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3393, c_3383, c_134])).
% 5.89/2.13  tff(c_3472, plain, (![A_395, B_396]: (r1_tarski(A_395, B_396) | ~m1_subset_1(A_395, k1_zfmisc_1(B_396)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.89/2.13  tff(c_3480, plain, (r1_tarski('#skF_11', '#skF_9')), inference(resolution, [status(thm)], [c_3443, c_3472])).
% 5.89/2.13  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.89/2.13  tff(c_3495, plain, ('#skF_11'='#skF_9' | ~r1_tarski('#skF_9', '#skF_11')), inference(resolution, [status(thm)], [c_3480, c_12])).
% 5.89/2.13  tff(c_3498, plain, ('#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3378, c_3495])).
% 5.89/2.13  tff(c_3503, plain, (v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3498, c_138])).
% 5.89/2.13  tff(c_120, plain, (![A_65, B_66]: (v1_xboole_0('#skF_8'(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.89/2.13  tff(c_3568, plain, (![A_404, B_405]: (r2_hidden('#skF_2'(A_404, B_405), A_404) | r1_tarski(A_404, B_405))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.89/2.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.89/2.13  tff(c_3573, plain, (![A_406, B_407]: (~v1_xboole_0(A_406) | r1_tarski(A_406, B_407))), inference(resolution, [status(thm)], [c_3568, c_2])).
% 5.89/2.13  tff(c_3481, plain, (![B_397, A_398]: (B_397=A_398 | ~r1_tarski(B_397, A_398) | ~r1_tarski(A_398, B_397))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.89/2.13  tff(c_3489, plain, (![A_12]: (A_12='#skF_9' | ~r1_tarski(A_12, '#skF_9'))), inference(resolution, [status(thm)], [c_3378, c_3481])).
% 5.89/2.13  tff(c_3582, plain, (![A_408]: (A_408='#skF_9' | ~v1_xboole_0(A_408))), inference(resolution, [status(thm)], [c_3573, c_3489])).
% 5.89/2.13  tff(c_3586, plain, (![A_65, B_66]: ('#skF_8'(A_65, B_66)='#skF_9')), inference(resolution, [status(thm)], [c_120, c_3582])).
% 5.89/2.13  tff(c_114, plain, (![A_65, B_66]: (v5_relat_1('#skF_8'(A_65, B_66), B_66))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.89/2.13  tff(c_3599, plain, (![B_66]: (v5_relat_1('#skF_9', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_3586, c_114])).
% 5.89/2.13  tff(c_3936, plain, (![B_450, A_451]: (r1_tarski(k2_relat_1(B_450), A_451) | ~v5_relat_1(B_450, A_451) | ~v1_relat_1(B_450))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.89/2.13  tff(c_4113, plain, (![B_466]: (k2_relat_1(B_466)='#skF_9' | ~v5_relat_1(B_466, '#skF_9') | ~v1_relat_1(B_466))), inference(resolution, [status(thm)], [c_3936, c_3489])).
% 5.89/2.13  tff(c_4129, plain, (k2_relat_1('#skF_9')='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3599, c_4113])).
% 5.89/2.13  tff(c_4141, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3403, c_4129])).
% 5.89/2.13  tff(c_116, plain, (![A_65, B_66]: (v4_relat_1('#skF_8'(A_65, B_66), A_65))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.89/2.13  tff(c_3600, plain, (![A_65]: (v4_relat_1('#skF_9', A_65))), inference(demodulation, [status(thm), theory('equality')], [c_3586, c_116])).
% 5.89/2.13  tff(c_3774, plain, (![B_437, A_438]: (r1_tarski(k1_relat_1(B_437), A_438) | ~v4_relat_1(B_437, A_438) | ~v1_relat_1(B_437))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.89/2.13  tff(c_3836, plain, (![B_440]: (k1_relat_1(B_440)='#skF_9' | ~v4_relat_1(B_440, '#skF_9') | ~v1_relat_1(B_440))), inference(resolution, [status(thm)], [c_3774, c_3489])).
% 5.89/2.13  tff(c_3840, plain, (k1_relat_1('#skF_9')='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_3600, c_3836])).
% 5.89/2.13  tff(c_3843, plain, (k1_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3403, c_3840])).
% 5.89/2.13  tff(c_5191, plain, (![E_559, B_560]: (r2_hidden(E_559, k1_funct_2(k1_relat_1(E_559), B_560)) | ~r1_tarski(k2_relat_1(E_559), B_560) | ~v1_funct_1(E_559) | ~v1_relat_1(E_559))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.89/2.13  tff(c_5201, plain, (![B_560]: (r2_hidden('#skF_9', k1_funct_2('#skF_9', B_560)) | ~r1_tarski(k2_relat_1('#skF_9'), B_560) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3843, c_5191])).
% 5.89/2.13  tff(c_5209, plain, (![B_560]: (r2_hidden('#skF_9', k1_funct_2('#skF_9', B_560)))), inference(demodulation, [status(thm), theory('equality')], [c_3403, c_3503, c_3378, c_4141, c_5201])).
% 5.89/2.13  tff(c_3404, plain, (~r2_hidden('#skF_11', k1_funct_2('#skF_9', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3383, c_130])).
% 5.89/2.13  tff(c_3501, plain, (~r2_hidden('#skF_9', k1_funct_2('#skF_9', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3498, c_3404])).
% 5.89/2.13  tff(c_5212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5209, c_3501])).
% 5.89/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.13  
% 5.89/2.13  Inference rules
% 5.89/2.13  ----------------------
% 5.89/2.13  #Ref     : 0
% 5.89/2.13  #Sup     : 1097
% 5.89/2.13  #Fact    : 0
% 5.89/2.13  #Define  : 0
% 5.89/2.13  #Split   : 9
% 5.89/2.13  #Chain   : 0
% 5.89/2.13  #Close   : 0
% 5.89/2.13  
% 5.89/2.13  Ordering : KBO
% 5.89/2.13  
% 5.89/2.13  Simplification rules
% 5.89/2.13  ----------------------
% 5.89/2.13  #Subsume      : 148
% 5.89/2.13  #Demod        : 940
% 5.89/2.13  #Tautology    : 537
% 5.89/2.13  #SimpNegUnit  : 5
% 5.89/2.13  #BackRed      : 69
% 5.89/2.13  
% 5.89/2.13  #Partial instantiations: 0
% 5.89/2.13  #Strategies tried      : 1
% 5.89/2.13  
% 5.89/2.13  Timing (in seconds)
% 5.89/2.13  ----------------------
% 5.89/2.13  Preprocessing        : 0.39
% 5.89/2.13  Parsing              : 0.18
% 5.89/2.13  CNF conversion       : 0.03
% 5.89/2.13  Main loop            : 0.98
% 5.89/2.13  Inferencing          : 0.34
% 5.89/2.13  Reduction            : 0.31
% 5.89/2.13  Demodulation         : 0.22
% 5.89/2.13  BG Simplification    : 0.05
% 5.89/2.13  Subsumption          : 0.18
% 5.89/2.13  Abstraction          : 0.04
% 5.89/2.13  MUC search           : 0.00
% 5.89/2.13  Cooper               : 0.00
% 5.89/2.13  Total                : 1.40
% 5.89/2.13  Index Insertion      : 0.00
% 5.89/2.13  Index Deletion       : 0.00
% 5.89/2.13  Index Matching       : 0.00
% 5.89/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
