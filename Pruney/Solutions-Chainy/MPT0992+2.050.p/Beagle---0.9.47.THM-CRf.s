%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:38 EST 2020

% Result     : Theorem 13.96s
% Output     : CNFRefutation 13.96s
% Verified   : 
% Statistics : Number of formulae       :  185 (1300 expanded)
%              Number of leaves         :   36 ( 419 expanded)
%              Depth                    :   15
%              Number of atoms          :  326 (4268 expanded)
%              Number of equality atoms :   94 (1609 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_153,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_36778,plain,(
    ! [C_1123,A_1124,B_1125] :
      ( v1_relat_1(C_1123)
      | ~ m1_subset_1(C_1123,k1_zfmisc_1(k2_zfmisc_1(A_1124,B_1125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36786,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_36778])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_37726,plain,(
    ! [A_1191,B_1192,C_1193] :
      ( k1_relset_1(A_1191,B_1192,C_1193) = k1_relat_1(C_1193)
      | ~ m1_subset_1(C_1193,k1_zfmisc_1(k2_zfmisc_1(A_1191,B_1192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_37740,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_37726])).

tff(c_39038,plain,(
    ! [B_1271,A_1272,C_1273] :
      ( k1_xboole_0 = B_1271
      | k1_relset_1(A_1272,B_1271,C_1273) = A_1272
      | ~ v1_funct_2(C_1273,A_1272,B_1271)
      | ~ m1_subset_1(C_1273,k1_zfmisc_1(k2_zfmisc_1(A_1272,B_1271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_39047,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_39038])).

tff(c_39061,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_37740,c_39047])).

tff(c_39062,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_39061])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_39082,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39062,c_22])).

tff(c_39092,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36786,c_39082])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_38571,plain,(
    ! [A_1251,B_1252,C_1253,D_1254] :
      ( k2_partfun1(A_1251,B_1252,C_1253,D_1254) = k7_relat_1(C_1253,D_1254)
      | ~ m1_subset_1(C_1253,k1_zfmisc_1(k2_zfmisc_1(A_1251,B_1252)))
      | ~ v1_funct_1(C_1253) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_38575,plain,(
    ! [D_1254] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1254) = k7_relat_1('#skF_4',D_1254)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_38571])).

tff(c_38585,plain,(
    ! [D_1254] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1254) = k7_relat_1('#skF_4',D_1254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_38575])).

tff(c_3681,plain,(
    ! [C_332,A_333,B_334] :
      ( v1_relat_1(C_332)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_333,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3689,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3681])).

tff(c_3899,plain,(
    ! [B_363,A_364] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_363,A_364)),k1_relat_1(B_363))
      | ~ v1_relat_1(B_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3776,plain,(
    ! [C_345,A_346,B_347] :
      ( v4_relat_1(C_345,A_346)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(A_346,B_347))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3786,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_3776])).

tff(c_3816,plain,(
    ! [B_352,A_353] :
      ( k7_relat_1(B_352,A_353) = B_352
      | ~ v4_relat_1(B_352,A_353)
      | ~ v1_relat_1(B_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3819,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3786,c_3816])).

tff(c_3822,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3689,c_3819])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3826,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3822,c_16])).

tff(c_3836,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3689,c_3826])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3847,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_1')
      | ~ r1_tarski(A_1,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3836,c_2])).

tff(c_3903,plain,(
    ! [A_364] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_364)),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3899,c_3847])).

tff(c_3927,plain,(
    ! [A_364] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_364)),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3689,c_3903])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6038,plain,(
    ! [B_503,A_504] :
      ( k1_relat_1(k7_relat_1(B_503,A_504)) = A_504
      | ~ r1_tarski(A_504,k1_relat_1(B_503))
      | ~ v1_relat_1(B_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6070,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,k1_relat_1(k7_relat_1(B_16,A_15)))) = k1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_20,c_6038])).

tff(c_6185,plain,(
    ! [A_515,B_516,C_517] :
      ( k1_relset_1(A_515,B_516,C_517) = k1_relat_1(C_517)
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(A_515,B_516))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_6195,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_6185])).

tff(c_8007,plain,(
    ! [B_627,A_628,C_629] :
      ( k1_xboole_0 = B_627
      | k1_relset_1(A_628,B_627,C_629) = A_628
      | ~ v1_funct_2(C_629,A_628,B_627)
      | ~ m1_subset_1(C_629,k1_zfmisc_1(k2_zfmisc_1(A_628,B_627))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_8016,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_8007])).

tff(c_8031,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6195,c_8016])).

tff(c_8032,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_8031])).

tff(c_8060,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8032,c_22])).

tff(c_8369,plain,(
    ! [A_649] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_649)) = A_649
      | ~ r1_tarski(A_649,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3689,c_8060])).

tff(c_6784,plain,(
    ! [B_558,A_559] :
      ( k1_relat_1(k7_relat_1(B_558,k1_relat_1(k7_relat_1(B_558,A_559)))) = k1_relat_1(k7_relat_1(B_558,A_559))
      | ~ v1_relat_1(B_558) ) ),
    inference(resolution,[status(thm)],[c_20,c_6038])).

tff(c_6839,plain,(
    ! [B_558,A_559] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_558,A_559)),k1_relat_1(k7_relat_1(B_558,A_559)))
      | ~ v1_relat_1(B_558)
      | ~ v1_relat_1(B_558) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6784,c_16])).

tff(c_8389,plain,(
    ! [A_649] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_649)),A_649)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_649,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8369,c_6839])).

tff(c_8760,plain,(
    ! [A_660] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_660)),A_660)
      | ~ r1_tarski(A_660,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3689,c_3689,c_8389])).

tff(c_8823,plain,(
    ! [A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_15)),k1_relat_1(k7_relat_1('#skF_4',A_15)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_15)),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6070,c_8760])).

tff(c_9333,plain,(
    ! [A_664] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_664)),k1_relat_1(k7_relat_1('#skF_4',A_664))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3689,c_3927,c_8823])).

tff(c_3690,plain,(
    ! [A_335,C_336,B_337] :
      ( r1_tarski(A_335,C_336)
      | ~ r1_tarski(B_337,C_336)
      | ~ r1_tarski(A_335,B_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3700,plain,(
    ! [A_335,A_11,B_12] :
      ( r1_tarski(A_335,A_11)
      | ~ r1_tarski(A_335,k1_relat_1(k7_relat_1(B_12,A_11)))
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_3690])).

tff(c_9344,plain,(
    ! [A_664] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_664)),A_664)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9333,c_3700])).

tff(c_9411,plain,(
    ! [A_664] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_664)),A_664) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3689,c_9344])).

tff(c_7576,plain,(
    ! [A_595,B_596,C_597,D_598] :
      ( k2_partfun1(A_595,B_596,C_597,D_598) = k7_relat_1(C_597,D_598)
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(A_595,B_596)))
      | ~ v1_funct_1(C_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_7578,plain,(
    ! [D_598] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_598) = k7_relat_1('#skF_4',D_598)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_7576])).

tff(c_7585,plain,(
    ! [D_598] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_598) = k7_relat_1('#skF_4',D_598) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_7578])).

tff(c_8107,plain,(
    ! [A_632,B_633,C_634,D_635] :
      ( m1_subset_1(k2_partfun1(A_632,B_633,C_634,D_635),k1_zfmisc_1(k2_zfmisc_1(A_632,B_633)))
      | ~ m1_subset_1(C_634,k1_zfmisc_1(k2_zfmisc_1(A_632,B_633)))
      | ~ v1_funct_1(C_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    ! [D_33,B_31,C_32,A_30] :
      ( m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(B_31,C_32)))
      | ~ r1_tarski(k1_relat_1(D_33),B_31)
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1(A_30,C_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_19903,plain,(
    ! [B_847,A_850,D_849,B_846,C_848] :
      ( m1_subset_1(k2_partfun1(A_850,B_846,C_848,D_849),k1_zfmisc_1(k2_zfmisc_1(B_847,B_846)))
      | ~ r1_tarski(k1_relat_1(k2_partfun1(A_850,B_846,C_848,D_849)),B_847)
      | ~ m1_subset_1(C_848,k1_zfmisc_1(k2_zfmisc_1(A_850,B_846)))
      | ~ v1_funct_1(C_848) ) ),
    inference(resolution,[status(thm)],[c_8107,c_34])).

tff(c_19945,plain,(
    ! [D_598,B_847] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_598),k1_zfmisc_1(k2_zfmisc_1(B_847,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_598)),B_847)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7585,c_19903])).

tff(c_36654,plain,(
    ! [D_1117,B_1118] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_1117),k1_zfmisc_1(k2_zfmisc_1(B_1118,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_1117)),B_1118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_7585,c_19945])).

tff(c_1480,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( v1_funct_1(k2_partfun1(A_165,B_166,C_167,D_168))
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ v1_funct_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1482,plain,(
    ! [D_168] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_168))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_1480])).

tff(c_1489,plain,(
    ! [D_168] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_168)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1482])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_95,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_1492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1489,c_95])).

tff(c_1493,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1496,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1493])).

tff(c_7587,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7585,c_1496])).

tff(c_36690,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_36654,c_7587])).

tff(c_36757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9411,c_36690])).

tff(c_36759,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1493])).

tff(c_37739,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36759,c_37726])).

tff(c_38596,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38585,c_38585,c_37739])).

tff(c_36758,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1493])).

tff(c_38601,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38585,c_36758])).

tff(c_38600,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38585,c_36759])).

tff(c_38780,plain,(
    ! [B_1264,C_1265,A_1266] :
      ( k1_xboole_0 = B_1264
      | v1_funct_2(C_1265,A_1266,B_1264)
      | k1_relset_1(A_1266,B_1264,C_1265) != A_1266
      | ~ m1_subset_1(C_1265,k1_zfmisc_1(k2_zfmisc_1(A_1266,B_1264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38786,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_38600,c_38780])).

tff(c_38801,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38601,c_71,c_38786])).

tff(c_39774,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38596,c_38801])).

tff(c_39781,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_39092,c_39774])).

tff(c_39788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_39781])).

tff(c_39789,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39802,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39789,c_39789,c_10])).

tff(c_39790,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_39795,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39789,c_39790])).

tff(c_39801,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39795,c_62])).

tff(c_39803,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39802,c_39801])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39811,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39789,c_39789,c_8])).

tff(c_42012,plain,(
    ! [C_1518,A_1519,B_1520] :
      ( v1_relat_1(C_1518)
      | ~ m1_subset_1(C_1518,k1_zfmisc_1(k2_zfmisc_1(A_1519,B_1520))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42017,plain,(
    ! [C_1521] :
      ( v1_relat_1(C_1521)
      | ~ m1_subset_1(C_1521,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39811,c_42012])).

tff(c_42021,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_39803,c_42017])).

tff(c_42092,plain,(
    ! [C_1531,A_1532,B_1533] :
      ( v4_relat_1(C_1531,A_1532)
      | ~ m1_subset_1(C_1531,k1_zfmisc_1(k2_zfmisc_1(A_1532,B_1533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42099,plain,(
    ! [C_1534,A_1535] :
      ( v4_relat_1(C_1534,A_1535)
      | ~ m1_subset_1(C_1534,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39811,c_42092])).

tff(c_42102,plain,(
    ! [A_1535] : v4_relat_1('#skF_4',A_1535) ),
    inference(resolution,[status(thm)],[c_39803,c_42099])).

tff(c_42111,plain,(
    ! [B_1540,A_1541] :
      ( k7_relat_1(B_1540,A_1541) = B_1540
      | ~ v4_relat_1(B_1540,A_1541)
      | ~ v1_relat_1(B_1540) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42114,plain,(
    ! [A_1535] :
      ( k7_relat_1('#skF_4',A_1535) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42102,c_42111])).

tff(c_42117,plain,(
    ! [A_1535] : k7_relat_1('#skF_4',A_1535) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42021,c_42114])).

tff(c_43938,plain,(
    ! [A_1700,B_1701,C_1702,D_1703] :
      ( k2_partfun1(A_1700,B_1701,C_1702,D_1703) = k7_relat_1(C_1702,D_1703)
      | ~ m1_subset_1(C_1702,k1_zfmisc_1(k2_zfmisc_1(A_1700,B_1701)))
      | ~ v1_funct_1(C_1702) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44119,plain,(
    ! [A_1711,C_1712,D_1713] :
      ( k2_partfun1(A_1711,'#skF_1',C_1712,D_1713) = k7_relat_1(C_1712,D_1713)
      | ~ m1_subset_1(C_1712,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1712) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39811,c_43938])).

tff(c_44123,plain,(
    ! [A_1711,D_1713] :
      ( k2_partfun1(A_1711,'#skF_1','#skF_4',D_1713) = k7_relat_1('#skF_4',D_1713)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39803,c_44119])).

tff(c_44128,plain,(
    ! [A_1711,D_1713] : k2_partfun1(A_1711,'#skF_1','#skF_4',D_1713) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42117,c_44123])).

tff(c_40725,plain,(
    ! [A_1388,B_1389,C_1390,D_1391] :
      ( v1_funct_1(k2_partfun1(A_1388,B_1389,C_1390,D_1391))
      | ~ m1_subset_1(C_1390,k1_zfmisc_1(k2_zfmisc_1(A_1388,B_1389)))
      | ~ v1_funct_1(C_1390) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40730,plain,(
    ! [A_1392,C_1393,D_1394] :
      ( v1_funct_1(k2_partfun1(A_1392,'#skF_1',C_1393,D_1394))
      | ~ m1_subset_1(C_1393,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39811,c_40725])).

tff(c_40732,plain,(
    ! [A_1392,D_1394] :
      ( v1_funct_1(k2_partfun1(A_1392,'#skF_1','#skF_4',D_1394))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_39803,c_40730])).

tff(c_40735,plain,(
    ! [A_1392,D_1394] : v1_funct_1(k2_partfun1(A_1392,'#skF_1','#skF_4',D_1394)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_40732])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39828,plain,(
    ! [A_1299] :
      ( A_1299 = '#skF_1'
      | ~ r1_tarski(A_1299,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39789,c_39789,c_4])).

tff(c_39832,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_39828])).

tff(c_39850,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39832,c_39795,c_39832,c_39832,c_39795,c_39795,c_39832,c_39811,c_39795,c_39795,c_56])).

tff(c_39851,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_39850])).

tff(c_40738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40735,c_39851])).

tff(c_40739,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_39850])).

tff(c_41992,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_40739])).

tff(c_44130,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44128,c_41992])).

tff(c_44134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39803,c_44130])).

tff(c_44136,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_40739])).

tff(c_44137,plain,(
    ! [C_1714,A_1715,B_1716] :
      ( v1_relat_1(C_1714)
      | ~ m1_subset_1(C_1714,k1_zfmisc_1(k2_zfmisc_1(A_1715,B_1716))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44139,plain,(
    ! [C_1714] :
      ( v1_relat_1(C_1714)
      | ~ m1_subset_1(C_1714,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39811,c_44137])).

tff(c_44150,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44136,c_44139])).

tff(c_44241,plain,(
    ! [C_1730,A_1731,B_1732] :
      ( v4_relat_1(C_1730,A_1731)
      | ~ m1_subset_1(C_1730,k1_zfmisc_1(k2_zfmisc_1(A_1731,B_1732))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44255,plain,(
    ! [C_1736,A_1737] :
      ( v4_relat_1(C_1736,A_1737)
      | ~ m1_subset_1(C_1736,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39811,c_44241])).

tff(c_44351,plain,(
    ! [A_1742] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1742) ),
    inference(resolution,[status(thm)],[c_44136,c_44255])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44354,plain,(
    ! [A_1742] :
      ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1742) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_44351,c_14])).

tff(c_44380,plain,(
    ! [A_1748] : k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_1748) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44150,c_44354])).

tff(c_41950,plain,(
    ! [B_1511,A_1512] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_1511,A_1512)),A_1512)
      | ~ v1_relat_1(B_1511) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_39827,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39789,c_39789,c_4])).

tff(c_41958,plain,(
    ! [B_1511] :
      ( k1_relat_1(k7_relat_1(B_1511,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_1511) ) ),
    inference(resolution,[status(thm)],[c_41950,c_39827])).

tff(c_44393,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44380,c_41958])).

tff(c_44411,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44150,c_44393])).

tff(c_44611,plain,(
    ! [A_1762,B_1763,C_1764] :
      ( k1_relset_1(A_1762,B_1763,C_1764) = k1_relat_1(C_1764)
      | ~ m1_subset_1(C_1764,k1_zfmisc_1(k2_zfmisc_1(A_1762,B_1763))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44641,plain,(
    ! [B_1769,C_1770] :
      ( k1_relset_1('#skF_1',B_1769,C_1770) = k1_relat_1(C_1770)
      | ~ m1_subset_1(C_1770,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39802,c_44611])).

tff(c_44643,plain,(
    ! [B_1769] : k1_relset_1('#skF_1',B_1769,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44136,c_44641])).

tff(c_44647,plain,(
    ! [B_1769] : k1_relset_1('#skF_1',B_1769,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44411,c_44643])).

tff(c_42,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_68,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_42])).

tff(c_44764,plain,(
    ! [C_1794,B_1795] :
      ( v1_funct_2(C_1794,'#skF_1',B_1795)
      | k1_relset_1('#skF_1',B_1795,C_1794) != '#skF_1'
      | ~ m1_subset_1(C_1794,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39789,c_39789,c_39789,c_39789,c_68])).

tff(c_44766,plain,(
    ! [B_1795] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_1795)
      | k1_relset_1('#skF_1',B_1795,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_44136,c_44764])).

tff(c_44771,plain,(
    ! [B_1795] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_1795) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44647,c_44766])).

tff(c_44135,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40739])).

tff(c_44791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44771,c_44135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.96/5.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.96/5.81  
% 13.96/5.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.96/5.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.96/5.81  
% 13.96/5.81  %Foreground sorts:
% 13.96/5.81  
% 13.96/5.81  
% 13.96/5.81  %Background operators:
% 13.96/5.81  
% 13.96/5.81  
% 13.96/5.81  %Foreground operators:
% 13.96/5.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.96/5.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.96/5.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.96/5.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.96/5.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.96/5.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.96/5.81  tff('#skF_2', type, '#skF_2': $i).
% 13.96/5.81  tff('#skF_3', type, '#skF_3': $i).
% 13.96/5.81  tff('#skF_1', type, '#skF_1': $i).
% 13.96/5.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.96/5.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.96/5.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.96/5.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.96/5.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.96/5.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.96/5.81  tff('#skF_4', type, '#skF_4': $i).
% 13.96/5.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.96/5.81  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.96/5.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.96/5.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.96/5.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.96/5.81  
% 13.96/5.83  tff(f_153, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 13.96/5.83  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.96/5.83  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.96/5.83  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.96/5.83  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 13.96/5.83  tff(f_133, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 13.96/5.83  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 13.96/5.83  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.96/5.83  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 13.96/5.83  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 13.96/5.83  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 13.96/5.83  tff(f_127, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 13.96/5.83  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 13.96/5.83  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.96/5.83  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 13.96/5.83  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.96/5.83  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.96/5.83  tff(c_36778, plain, (![C_1123, A_1124, B_1125]: (v1_relat_1(C_1123) | ~m1_subset_1(C_1123, k1_zfmisc_1(k2_zfmisc_1(A_1124, B_1125))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.96/5.83  tff(c_36786, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_36778])).
% 13.96/5.83  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.96/5.83  tff(c_71, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 13.96/5.83  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.96/5.83  tff(c_37726, plain, (![A_1191, B_1192, C_1193]: (k1_relset_1(A_1191, B_1192, C_1193)=k1_relat_1(C_1193) | ~m1_subset_1(C_1193, k1_zfmisc_1(k2_zfmisc_1(A_1191, B_1192))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.96/5.83  tff(c_37740, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_37726])).
% 13.96/5.83  tff(c_39038, plain, (![B_1271, A_1272, C_1273]: (k1_xboole_0=B_1271 | k1_relset_1(A_1272, B_1271, C_1273)=A_1272 | ~v1_funct_2(C_1273, A_1272, B_1271) | ~m1_subset_1(C_1273, k1_zfmisc_1(k2_zfmisc_1(A_1272, B_1271))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.96/5.83  tff(c_39047, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_39038])).
% 13.96/5.83  tff(c_39061, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_37740, c_39047])).
% 13.96/5.83  tff(c_39062, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_39061])).
% 13.96/5.83  tff(c_22, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.96/5.83  tff(c_39082, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39062, c_22])).
% 13.96/5.83  tff(c_39092, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36786, c_39082])).
% 13.96/5.83  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.96/5.83  tff(c_38571, plain, (![A_1251, B_1252, C_1253, D_1254]: (k2_partfun1(A_1251, B_1252, C_1253, D_1254)=k7_relat_1(C_1253, D_1254) | ~m1_subset_1(C_1253, k1_zfmisc_1(k2_zfmisc_1(A_1251, B_1252))) | ~v1_funct_1(C_1253))), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.96/5.83  tff(c_38575, plain, (![D_1254]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1254)=k7_relat_1('#skF_4', D_1254) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_38571])).
% 13.96/5.83  tff(c_38585, plain, (![D_1254]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1254)=k7_relat_1('#skF_4', D_1254))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_38575])).
% 13.96/5.83  tff(c_3681, plain, (![C_332, A_333, B_334]: (v1_relat_1(C_332) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.96/5.83  tff(c_3689, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3681])).
% 13.96/5.83  tff(c_3899, plain, (![B_363, A_364]: (r1_tarski(k1_relat_1(k7_relat_1(B_363, A_364)), k1_relat_1(B_363)) | ~v1_relat_1(B_363))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.96/5.83  tff(c_3776, plain, (![C_345, A_346, B_347]: (v4_relat_1(C_345, A_346) | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(A_346, B_347))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.96/5.83  tff(c_3786, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_3776])).
% 13.96/5.83  tff(c_3816, plain, (![B_352, A_353]: (k7_relat_1(B_352, A_353)=B_352 | ~v4_relat_1(B_352, A_353) | ~v1_relat_1(B_352))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.96/5.83  tff(c_3819, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3786, c_3816])).
% 13.96/5.83  tff(c_3822, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3689, c_3819])).
% 13.96/5.83  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.96/5.83  tff(c_3826, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3822, c_16])).
% 13.96/5.83  tff(c_3836, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3689, c_3826])).
% 13.96/5.83  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.96/5.83  tff(c_3847, plain, (![A_1]: (r1_tarski(A_1, '#skF_1') | ~r1_tarski(A_1, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_3836, c_2])).
% 13.96/5.83  tff(c_3903, plain, (![A_364]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_364)), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3899, c_3847])).
% 13.96/5.83  tff(c_3927, plain, (![A_364]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_364)), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3689, c_3903])).
% 13.96/5.83  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.96/5.83  tff(c_6038, plain, (![B_503, A_504]: (k1_relat_1(k7_relat_1(B_503, A_504))=A_504 | ~r1_tarski(A_504, k1_relat_1(B_503)) | ~v1_relat_1(B_503))), inference(cnfTransformation, [status(thm)], [f_69])).
% 13.96/5.83  tff(c_6070, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, k1_relat_1(k7_relat_1(B_16, A_15))))=k1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_20, c_6038])).
% 13.96/5.83  tff(c_6185, plain, (![A_515, B_516, C_517]: (k1_relset_1(A_515, B_516, C_517)=k1_relat_1(C_517) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(A_515, B_516))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.96/5.83  tff(c_6195, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_6185])).
% 13.96/5.83  tff(c_8007, plain, (![B_627, A_628, C_629]: (k1_xboole_0=B_627 | k1_relset_1(A_628, B_627, C_629)=A_628 | ~v1_funct_2(C_629, A_628, B_627) | ~m1_subset_1(C_629, k1_zfmisc_1(k2_zfmisc_1(A_628, B_627))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.96/5.83  tff(c_8016, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_8007])).
% 13.96/5.83  tff(c_8031, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6195, c_8016])).
% 13.96/5.83  tff(c_8032, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_8031])).
% 13.96/5.83  tff(c_8060, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8032, c_22])).
% 13.96/5.83  tff(c_8369, plain, (![A_649]: (k1_relat_1(k7_relat_1('#skF_4', A_649))=A_649 | ~r1_tarski(A_649, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3689, c_8060])).
% 13.96/5.83  tff(c_6784, plain, (![B_558, A_559]: (k1_relat_1(k7_relat_1(B_558, k1_relat_1(k7_relat_1(B_558, A_559))))=k1_relat_1(k7_relat_1(B_558, A_559)) | ~v1_relat_1(B_558))), inference(resolution, [status(thm)], [c_20, c_6038])).
% 13.96/5.83  tff(c_6839, plain, (![B_558, A_559]: (r1_tarski(k1_relat_1(k7_relat_1(B_558, A_559)), k1_relat_1(k7_relat_1(B_558, A_559))) | ~v1_relat_1(B_558) | ~v1_relat_1(B_558))), inference(superposition, [status(thm), theory('equality')], [c_6784, c_16])).
% 13.96/5.83  tff(c_8389, plain, (![A_649]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_649)), A_649) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(A_649, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8369, c_6839])).
% 13.96/5.83  tff(c_8760, plain, (![A_660]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_660)), A_660) | ~r1_tarski(A_660, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3689, c_3689, c_8389])).
% 13.96/5.83  tff(c_8823, plain, (![A_15]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_15)), k1_relat_1(k7_relat_1('#skF_4', A_15))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_15)), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6070, c_8760])).
% 13.96/5.83  tff(c_9333, plain, (![A_664]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_664)), k1_relat_1(k7_relat_1('#skF_4', A_664))))), inference(demodulation, [status(thm), theory('equality')], [c_3689, c_3927, c_8823])).
% 13.96/5.83  tff(c_3690, plain, (![A_335, C_336, B_337]: (r1_tarski(A_335, C_336) | ~r1_tarski(B_337, C_336) | ~r1_tarski(A_335, B_337))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.96/5.83  tff(c_3700, plain, (![A_335, A_11, B_12]: (r1_tarski(A_335, A_11) | ~r1_tarski(A_335, k1_relat_1(k7_relat_1(B_12, A_11))) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_16, c_3690])).
% 13.96/5.83  tff(c_9344, plain, (![A_664]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_664)), A_664) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9333, c_3700])).
% 13.96/5.83  tff(c_9411, plain, (![A_664]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_664)), A_664))), inference(demodulation, [status(thm), theory('equality')], [c_3689, c_9344])).
% 13.96/5.83  tff(c_7576, plain, (![A_595, B_596, C_597, D_598]: (k2_partfun1(A_595, B_596, C_597, D_598)=k7_relat_1(C_597, D_598) | ~m1_subset_1(C_597, k1_zfmisc_1(k2_zfmisc_1(A_595, B_596))) | ~v1_funct_1(C_597))), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.96/5.83  tff(c_7578, plain, (![D_598]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_598)=k7_relat_1('#skF_4', D_598) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_7576])).
% 13.96/5.83  tff(c_7585, plain, (![D_598]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_598)=k7_relat_1('#skF_4', D_598))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_7578])).
% 13.96/5.83  tff(c_8107, plain, (![A_632, B_633, C_634, D_635]: (m1_subset_1(k2_partfun1(A_632, B_633, C_634, D_635), k1_zfmisc_1(k2_zfmisc_1(A_632, B_633))) | ~m1_subset_1(C_634, k1_zfmisc_1(k2_zfmisc_1(A_632, B_633))) | ~v1_funct_1(C_634))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.96/5.83  tff(c_34, plain, (![D_33, B_31, C_32, A_30]: (m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(B_31, C_32))) | ~r1_tarski(k1_relat_1(D_33), B_31) | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1(A_30, C_32))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.96/5.83  tff(c_19903, plain, (![B_847, A_850, D_849, B_846, C_848]: (m1_subset_1(k2_partfun1(A_850, B_846, C_848, D_849), k1_zfmisc_1(k2_zfmisc_1(B_847, B_846))) | ~r1_tarski(k1_relat_1(k2_partfun1(A_850, B_846, C_848, D_849)), B_847) | ~m1_subset_1(C_848, k1_zfmisc_1(k2_zfmisc_1(A_850, B_846))) | ~v1_funct_1(C_848))), inference(resolution, [status(thm)], [c_8107, c_34])).
% 13.96/5.83  tff(c_19945, plain, (![D_598, B_847]: (m1_subset_1(k7_relat_1('#skF_4', D_598), k1_zfmisc_1(k2_zfmisc_1(B_847, '#skF_2'))) | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_598)), B_847) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7585, c_19903])).
% 13.96/5.83  tff(c_36654, plain, (![D_1117, B_1118]: (m1_subset_1(k7_relat_1('#skF_4', D_1117), k1_zfmisc_1(k2_zfmisc_1(B_1118, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_1117)), B_1118))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_7585, c_19945])).
% 13.96/5.83  tff(c_1480, plain, (![A_165, B_166, C_167, D_168]: (v1_funct_1(k2_partfun1(A_165, B_166, C_167, D_168)) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~v1_funct_1(C_167))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.96/5.83  tff(c_1482, plain, (![D_168]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_168)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1480])).
% 13.96/5.83  tff(c_1489, plain, (![D_168]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_168)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1482])).
% 13.96/5.83  tff(c_56, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 13.96/5.83  tff(c_95, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 13.96/5.83  tff(c_1492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1489, c_95])).
% 13.96/5.83  tff(c_1493, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 13.96/5.83  tff(c_1496, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1493])).
% 13.96/5.83  tff(c_7587, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7585, c_1496])).
% 13.96/5.83  tff(c_36690, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_36654, c_7587])).
% 13.96/5.83  tff(c_36757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9411, c_36690])).
% 13.96/5.83  tff(c_36759, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1493])).
% 13.96/5.83  tff(c_37739, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_36759, c_37726])).
% 13.96/5.83  tff(c_38596, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38585, c_38585, c_37739])).
% 13.96/5.83  tff(c_36758, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1493])).
% 13.96/5.83  tff(c_38601, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38585, c_36758])).
% 13.96/5.83  tff(c_38600, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38585, c_36759])).
% 13.96/5.83  tff(c_38780, plain, (![B_1264, C_1265, A_1266]: (k1_xboole_0=B_1264 | v1_funct_2(C_1265, A_1266, B_1264) | k1_relset_1(A_1266, B_1264, C_1265)!=A_1266 | ~m1_subset_1(C_1265, k1_zfmisc_1(k2_zfmisc_1(A_1266, B_1264))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.96/5.83  tff(c_38786, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_38600, c_38780])).
% 13.96/5.83  tff(c_38801, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38601, c_71, c_38786])).
% 13.96/5.83  tff(c_39774, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38596, c_38801])).
% 13.96/5.83  tff(c_39781, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_39092, c_39774])).
% 13.96/5.83  tff(c_39788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_39781])).
% 13.96/5.83  tff(c_39789, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 13.96/5.83  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.96/5.83  tff(c_39802, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39789, c_39789, c_10])).
% 13.96/5.83  tff(c_39790, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 13.96/5.83  tff(c_39795, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_39789, c_39790])).
% 13.96/5.83  tff(c_39801, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_39795, c_62])).
% 13.96/5.83  tff(c_39803, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_39802, c_39801])).
% 13.96/5.83  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.96/5.83  tff(c_39811, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_39789, c_39789, c_8])).
% 13.96/5.83  tff(c_42012, plain, (![C_1518, A_1519, B_1520]: (v1_relat_1(C_1518) | ~m1_subset_1(C_1518, k1_zfmisc_1(k2_zfmisc_1(A_1519, B_1520))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.96/5.83  tff(c_42017, plain, (![C_1521]: (v1_relat_1(C_1521) | ~m1_subset_1(C_1521, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_39811, c_42012])).
% 13.96/5.83  tff(c_42021, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_39803, c_42017])).
% 13.96/5.83  tff(c_42092, plain, (![C_1531, A_1532, B_1533]: (v4_relat_1(C_1531, A_1532) | ~m1_subset_1(C_1531, k1_zfmisc_1(k2_zfmisc_1(A_1532, B_1533))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.96/5.83  tff(c_42099, plain, (![C_1534, A_1535]: (v4_relat_1(C_1534, A_1535) | ~m1_subset_1(C_1534, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_39811, c_42092])).
% 13.96/5.83  tff(c_42102, plain, (![A_1535]: (v4_relat_1('#skF_4', A_1535))), inference(resolution, [status(thm)], [c_39803, c_42099])).
% 13.96/5.83  tff(c_42111, plain, (![B_1540, A_1541]: (k7_relat_1(B_1540, A_1541)=B_1540 | ~v4_relat_1(B_1540, A_1541) | ~v1_relat_1(B_1540))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.96/5.83  tff(c_42114, plain, (![A_1535]: (k7_relat_1('#skF_4', A_1535)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_42102, c_42111])).
% 13.96/5.83  tff(c_42117, plain, (![A_1535]: (k7_relat_1('#skF_4', A_1535)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42021, c_42114])).
% 13.96/5.83  tff(c_43938, plain, (![A_1700, B_1701, C_1702, D_1703]: (k2_partfun1(A_1700, B_1701, C_1702, D_1703)=k7_relat_1(C_1702, D_1703) | ~m1_subset_1(C_1702, k1_zfmisc_1(k2_zfmisc_1(A_1700, B_1701))) | ~v1_funct_1(C_1702))), inference(cnfTransformation, [status(thm)], [f_133])).
% 13.96/5.83  tff(c_44119, plain, (![A_1711, C_1712, D_1713]: (k2_partfun1(A_1711, '#skF_1', C_1712, D_1713)=k7_relat_1(C_1712, D_1713) | ~m1_subset_1(C_1712, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1712))), inference(superposition, [status(thm), theory('equality')], [c_39811, c_43938])).
% 13.96/5.83  tff(c_44123, plain, (![A_1711, D_1713]: (k2_partfun1(A_1711, '#skF_1', '#skF_4', D_1713)=k7_relat_1('#skF_4', D_1713) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_39803, c_44119])).
% 13.96/5.83  tff(c_44128, plain, (![A_1711, D_1713]: (k2_partfun1(A_1711, '#skF_1', '#skF_4', D_1713)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42117, c_44123])).
% 13.96/5.83  tff(c_40725, plain, (![A_1388, B_1389, C_1390, D_1391]: (v1_funct_1(k2_partfun1(A_1388, B_1389, C_1390, D_1391)) | ~m1_subset_1(C_1390, k1_zfmisc_1(k2_zfmisc_1(A_1388, B_1389))) | ~v1_funct_1(C_1390))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.96/5.83  tff(c_40730, plain, (![A_1392, C_1393, D_1394]: (v1_funct_1(k2_partfun1(A_1392, '#skF_1', C_1393, D_1394)) | ~m1_subset_1(C_1393, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1393))), inference(superposition, [status(thm), theory('equality')], [c_39811, c_40725])).
% 13.96/5.83  tff(c_40732, plain, (![A_1392, D_1394]: (v1_funct_1(k2_partfun1(A_1392, '#skF_1', '#skF_4', D_1394)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_39803, c_40730])).
% 13.96/5.83  tff(c_40735, plain, (![A_1392, D_1394]: (v1_funct_1(k2_partfun1(A_1392, '#skF_1', '#skF_4', D_1394)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_40732])).
% 13.96/5.83  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.96/5.83  tff(c_39828, plain, (![A_1299]: (A_1299='#skF_1' | ~r1_tarski(A_1299, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_39789, c_39789, c_4])).
% 13.96/5.83  tff(c_39832, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_39828])).
% 13.96/5.83  tff(c_39850, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_39832, c_39795, c_39832, c_39832, c_39795, c_39795, c_39832, c_39811, c_39795, c_39795, c_56])).
% 13.96/5.83  tff(c_39851, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_39850])).
% 13.96/5.83  tff(c_40738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40735, c_39851])).
% 13.96/5.83  tff(c_40739, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_39850])).
% 13.96/5.83  tff(c_41992, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_40739])).
% 13.96/5.83  tff(c_44130, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44128, c_41992])).
% 13.96/5.83  tff(c_44134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39803, c_44130])).
% 13.96/5.83  tff(c_44136, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_40739])).
% 13.96/5.83  tff(c_44137, plain, (![C_1714, A_1715, B_1716]: (v1_relat_1(C_1714) | ~m1_subset_1(C_1714, k1_zfmisc_1(k2_zfmisc_1(A_1715, B_1716))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.96/5.83  tff(c_44139, plain, (![C_1714]: (v1_relat_1(C_1714) | ~m1_subset_1(C_1714, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_39811, c_44137])).
% 13.96/5.83  tff(c_44150, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_44136, c_44139])).
% 13.96/5.83  tff(c_44241, plain, (![C_1730, A_1731, B_1732]: (v4_relat_1(C_1730, A_1731) | ~m1_subset_1(C_1730, k1_zfmisc_1(k2_zfmisc_1(A_1731, B_1732))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.96/5.83  tff(c_44255, plain, (![C_1736, A_1737]: (v4_relat_1(C_1736, A_1737) | ~m1_subset_1(C_1736, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_39811, c_44241])).
% 13.96/5.83  tff(c_44351, plain, (![A_1742]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1742))), inference(resolution, [status(thm)], [c_44136, c_44255])).
% 13.96/5.83  tff(c_14, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.96/5.83  tff(c_44354, plain, (![A_1742]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1742)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_44351, c_14])).
% 13.96/5.83  tff(c_44380, plain, (![A_1748]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_1748)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44150, c_44354])).
% 13.96/5.83  tff(c_41950, plain, (![B_1511, A_1512]: (r1_tarski(k1_relat_1(k7_relat_1(B_1511, A_1512)), A_1512) | ~v1_relat_1(B_1511))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.96/5.83  tff(c_39827, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_39789, c_39789, c_4])).
% 13.96/5.83  tff(c_41958, plain, (![B_1511]: (k1_relat_1(k7_relat_1(B_1511, '#skF_1'))='#skF_1' | ~v1_relat_1(B_1511))), inference(resolution, [status(thm)], [c_41950, c_39827])).
% 13.96/5.83  tff(c_44393, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44380, c_41958])).
% 13.96/5.83  tff(c_44411, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44150, c_44393])).
% 13.96/5.83  tff(c_44611, plain, (![A_1762, B_1763, C_1764]: (k1_relset_1(A_1762, B_1763, C_1764)=k1_relat_1(C_1764) | ~m1_subset_1(C_1764, k1_zfmisc_1(k2_zfmisc_1(A_1762, B_1763))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.96/5.83  tff(c_44641, plain, (![B_1769, C_1770]: (k1_relset_1('#skF_1', B_1769, C_1770)=k1_relat_1(C_1770) | ~m1_subset_1(C_1770, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_39802, c_44611])).
% 13.96/5.83  tff(c_44643, plain, (![B_1769]: (k1_relset_1('#skF_1', B_1769, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_44136, c_44641])).
% 13.96/5.83  tff(c_44647, plain, (![B_1769]: (k1_relset_1('#skF_1', B_1769, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44411, c_44643])).
% 13.96/5.83  tff(c_42, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_39))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.96/5.83  tff(c_68, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_42])).
% 13.96/5.83  tff(c_44764, plain, (![C_1794, B_1795]: (v1_funct_2(C_1794, '#skF_1', B_1795) | k1_relset_1('#skF_1', B_1795, C_1794)!='#skF_1' | ~m1_subset_1(C_1794, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_39789, c_39789, c_39789, c_39789, c_68])).
% 13.96/5.83  tff(c_44766, plain, (![B_1795]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_1795) | k1_relset_1('#skF_1', B_1795, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1')), inference(resolution, [status(thm)], [c_44136, c_44764])).
% 13.96/5.83  tff(c_44771, plain, (![B_1795]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_1795))), inference(demodulation, [status(thm), theory('equality')], [c_44647, c_44766])).
% 13.96/5.83  tff(c_44135, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_40739])).
% 13.96/5.83  tff(c_44791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44771, c_44135])).
% 13.96/5.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.96/5.83  
% 13.96/5.83  Inference rules
% 13.96/5.83  ----------------------
% 13.96/5.83  #Ref     : 0
% 13.96/5.83  #Sup     : 9745
% 13.96/5.83  #Fact    : 0
% 13.96/5.83  #Define  : 0
% 13.96/5.83  #Split   : 56
% 13.96/5.83  #Chain   : 0
% 13.96/5.83  #Close   : 0
% 13.96/5.83  
% 13.96/5.83  Ordering : KBO
% 13.96/5.83  
% 13.96/5.83  Simplification rules
% 13.96/5.83  ----------------------
% 13.96/5.83  #Subsume      : 3281
% 13.96/5.83  #Demod        : 10440
% 13.96/5.83  #Tautology    : 3764
% 13.96/5.83  #SimpNegUnit  : 228
% 13.96/5.83  #BackRed      : 90
% 13.96/5.83  
% 13.96/5.83  #Partial instantiations: 0
% 13.96/5.83  #Strategies tried      : 1
% 13.96/5.83  
% 13.96/5.83  Timing (in seconds)
% 13.96/5.83  ----------------------
% 13.96/5.84  Preprocessing        : 0.36
% 13.96/5.84  Parsing              : 0.20
% 13.96/5.84  CNF conversion       : 0.02
% 13.96/5.84  Main loop            : 4.64
% 13.96/5.84  Inferencing          : 1.17
% 13.96/5.84  Reduction            : 1.93
% 13.96/5.84  Demodulation         : 1.48
% 13.96/5.84  BG Simplification    : 0.10
% 13.96/5.84  Subsumption          : 1.16
% 13.96/5.84  Abstraction          : 0.16
% 13.96/5.84  MUC search           : 0.00
% 13.96/5.84  Cooper               : 0.00
% 13.96/5.84  Total                : 5.05
% 13.96/5.84  Index Insertion      : 0.00
% 13.96/5.84  Index Deletion       : 0.00
% 13.96/5.84  Index Matching       : 0.00
% 13.96/5.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
