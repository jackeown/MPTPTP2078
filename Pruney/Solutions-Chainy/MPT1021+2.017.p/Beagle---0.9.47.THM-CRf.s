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
% DateTime   : Thu Dec  3 10:16:02 EST 2020

% Result     : Theorem 12.57s
% Output     : CNFRefutation 12.77s
% Verified   : 
% Statistics : Number of formulae       :  393 (4567 expanded)
%              Number of leaves         :   50 (1594 expanded)
%              Depth                    :   18
%              Number of atoms          :  924 (13280 expanded)
%              Number of equality atoms :  190 (1521 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k11_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_178,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_147,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
         => ( ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(B,D) = k11_relat_1(C,D) )
           => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_165,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_137,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_60,plain,(
    ! [A_50] : k6_relat_1(A_50) = k6_partfun1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_28,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_75,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28])).

tff(c_16514,plain,(
    ! [A_1371,B_1372,D_1373] :
      ( r2_relset_1(A_1371,B_1372,D_1373,D_1373)
      | ~ m1_subset_1(D_1373,k1_zfmisc_1(k2_zfmisc_1(A_1371,B_1372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16522,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_75,c_16514])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_70,plain,(
    v3_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_16813,plain,(
    ! [A_1439,B_1440] :
      ( k2_funct_2(A_1439,B_1440) = k2_funct_1(B_1440)
      | ~ m1_subset_1(B_1440,k1_zfmisc_1(k2_zfmisc_1(A_1439,A_1439)))
      | ~ v3_funct_2(B_1440,A_1439,A_1439)
      | ~ v1_funct_2(B_1440,A_1439,A_1439)
      | ~ v1_funct_1(B_1440) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_16823,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16813])).

tff(c_16828,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_16823])).

tff(c_16797,plain,(
    ! [A_1437,B_1438] :
      ( v1_funct_1(k2_funct_2(A_1437,B_1438))
      | ~ m1_subset_1(B_1438,k1_zfmisc_1(k2_zfmisc_1(A_1437,A_1437)))
      | ~ v3_funct_2(B_1438,A_1437,A_1437)
      | ~ v1_funct_2(B_1438,A_1437,A_1437)
      | ~ v1_funct_1(B_1438) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_16807,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16797])).

tff(c_16812,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_16807])).

tff(c_16829,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16828,c_16812])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16524,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16514])).

tff(c_16389,plain,(
    ! [C_1332,A_1333,B_1334] :
      ( v1_relat_1(C_1332)
      | ~ m1_subset_1(C_1332,k1_zfmisc_1(k2_zfmisc_1(A_1333,B_1334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16402,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16389])).

tff(c_16435,plain,(
    ! [C_1344,B_1345,A_1346] :
      ( v5_relat_1(C_1344,B_1345)
      | ~ m1_subset_1(C_1344,k1_zfmisc_1(k2_zfmisc_1(A_1346,B_1345))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16448,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_16435])).

tff(c_16525,plain,(
    ! [B_1374,A_1375] :
      ( k2_relat_1(B_1374) = A_1375
      | ~ v2_funct_2(B_1374,A_1375)
      | ~ v5_relat_1(B_1374,A_1375)
      | ~ v1_relat_1(B_1374) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16534,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16448,c_16525])).

tff(c_16543,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16402,c_16534])).

tff(c_16544,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16543])).

tff(c_16606,plain,(
    ! [C_1393,B_1394,A_1395] :
      ( v2_funct_2(C_1393,B_1394)
      | ~ v3_funct_2(C_1393,A_1395,B_1394)
      | ~ v1_funct_1(C_1393)
      | ~ m1_subset_1(C_1393,k1_zfmisc_1(k2_zfmisc_1(A_1395,B_1394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16616,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16606])).

tff(c_16621,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_16616])).

tff(c_16623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16544,c_16621])).

tff(c_16624,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16543])).

tff(c_16638,plain,(
    ! [A_1398,B_1399,C_1400] :
      ( k2_relset_1(A_1398,B_1399,C_1400) = k2_relat_1(C_1400)
      | ~ m1_subset_1(C_1400,k1_zfmisc_1(k2_zfmisc_1(A_1398,B_1399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16648,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16638])).

tff(c_16652,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16624,c_16648])).

tff(c_16679,plain,(
    ! [C_1405,A_1406,B_1407] :
      ( v2_funct_1(C_1405)
      | ~ v3_funct_2(C_1405,A_1406,B_1407)
      | ~ v1_funct_1(C_1405)
      | ~ m1_subset_1(C_1405,k1_zfmisc_1(k2_zfmisc_1(A_1406,B_1407))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16689,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_16679])).

tff(c_16694,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_16689])).

tff(c_17951,plain,(
    ! [A_1520,B_1521,C_1522] :
      ( r2_hidden('#skF_1'(A_1520,B_1521,C_1522),A_1520)
      | r2_relset_1(A_1520,A_1520,B_1521,C_1522)
      | ~ m1_subset_1(C_1522,k1_zfmisc_1(k2_zfmisc_1(A_1520,A_1520)))
      | ~ m1_subset_1(B_1521,k1_zfmisc_1(k2_zfmisc_1(A_1520,A_1520))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_17962,plain,(
    ! [B_1523] :
      ( r2_hidden('#skF_1'('#skF_2',B_1523,'#skF_3'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_2',B_1523,'#skF_3')
      | ~ m1_subset_1(B_1523,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_68,c_17951])).

tff(c_17974,plain,
    ( r2_hidden('#skF_1'('#skF_2',k6_partfun1('#skF_2'),'#skF_3'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_17962])).

tff(c_17991,plain,(
    r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_17974])).

tff(c_26,plain,(
    ! [D_20,C_19,A_17,B_18] :
      ( D_20 = C_19
      | ~ r2_relset_1(A_17,B_18,C_19,D_20)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_17993,plain,
    ( k6_partfun1('#skF_2') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_17991,c_26])).

tff(c_17996,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_68,c_17993])).

tff(c_18609,plain,(
    ! [B_1562,C_1563,A_1564] :
      ( k6_partfun1(B_1562) = k5_relat_1(k2_funct_1(C_1563),C_1563)
      | k1_xboole_0 = B_1562
      | ~ v2_funct_1(C_1563)
      | k2_relset_1(A_1564,B_1562,C_1563) != B_1562
      | ~ m1_subset_1(C_1563,k1_zfmisc_1(k2_zfmisc_1(A_1564,B_1562)))
      | ~ v1_funct_2(C_1563,A_1564,B_1562)
      | ~ v1_funct_1(C_1563) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_18620,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_18609])).

tff(c_18630,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_16652,c_16694,c_17996,c_18620])).

tff(c_18636,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18630])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18638,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18636,c_2])).

tff(c_18116,plain,(
    ! [A_1537,B_1538] :
      ( m1_subset_1(k2_funct_2(A_1537,B_1538),k1_zfmisc_1(k2_zfmisc_1(A_1537,A_1537)))
      | ~ m1_subset_1(B_1538,k1_zfmisc_1(k2_zfmisc_1(A_1537,A_1537)))
      | ~ v3_funct_2(B_1538,A_1537,A_1537)
      | ~ v1_funct_2(B_1538,A_1537,A_1537)
      | ~ v1_funct_1(B_1538) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_18165,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16828,c_18116])).

tff(c_18184,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_18165])).

tff(c_17961,plain,(
    ! [B_1521] :
      ( r2_hidden('#skF_1'('#skF_2',B_1521,'#skF_3'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_2',B_1521,'#skF_3')
      | ~ m1_subset_1(B_1521,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_68,c_17951])).

tff(c_18236,plain,
    ( r2_hidden('#skF_1'('#skF_2',k2_funct_1('#skF_3'),'#skF_3'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_18184,c_17961])).

tff(c_18263,plain,(
    r2_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18236])).

tff(c_18347,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_18263,c_26])).

tff(c_18350,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18184,c_68,c_18347])).

tff(c_17041,plain,(
    ! [A_1461,B_1462] :
      ( m1_subset_1(k2_funct_2(A_1461,B_1462),k1_zfmisc_1(k2_zfmisc_1(A_1461,A_1461)))
      | ~ m1_subset_1(B_1462,k1_zfmisc_1(k2_zfmisc_1(A_1461,A_1461)))
      | ~ v3_funct_2(B_1462,A_1461,A_1461)
      | ~ v1_funct_2(B_1462,A_1461,A_1461)
      | ~ v1_funct_1(B_1462) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_17085,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16828,c_17041])).

tff(c_17102,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_17085])).

tff(c_17841,plain,(
    ! [B_1512,C_1513,E_1511,A_1508,F_1510,D_1509] :
      ( m1_subset_1(k1_partfun1(A_1508,B_1512,C_1513,D_1509,E_1511,F_1510),k1_zfmisc_1(k2_zfmisc_1(A_1508,D_1509)))
      | ~ m1_subset_1(F_1510,k1_zfmisc_1(k2_zfmisc_1(C_1513,D_1509)))
      | ~ v1_funct_1(F_1510)
      | ~ m1_subset_1(E_1511,k1_zfmisc_1(k2_zfmisc_1(A_1508,B_1512)))
      | ~ v1_funct_1(E_1511) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7034,plain,(
    ! [A_800,B_801,D_802] :
      ( r2_relset_1(A_800,B_801,D_802,D_802)
      | ~ m1_subset_1(D_802,k1_zfmisc_1(k2_zfmisc_1(A_800,B_801))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7042,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_75,c_7034])).

tff(c_366,plain,(
    ! [A_128,B_129,D_130] :
      ( r2_relset_1(A_128,B_129,D_130,D_130)
      | ~ m1_subset_1(D_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_374,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_75,c_366])).

tff(c_550,plain,(
    ! [A_175,B_176] :
      ( k2_funct_2(A_175,B_176) = k2_funct_1(B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k2_zfmisc_1(A_175,A_175)))
      | ~ v3_funct_2(B_176,A_175,A_175)
      | ~ v1_funct_2(B_176,A_175,A_175)
      | ~ v1_funct_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_560,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_550])).

tff(c_565,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_560])).

tff(c_533,plain,(
    ! [A_172,B_173] :
      ( v1_funct_1(k2_funct_2(A_172,B_173))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k2_zfmisc_1(A_172,A_172)))
      | ~ v3_funct_2(B_173,A_172,A_172)
      | ~ v1_funct_2(B_173,A_172,A_172)
      | ~ v1_funct_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_543,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_533])).

tff(c_548,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_543])).

tff(c_566,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_548])).

tff(c_376,plain,(
    r2_relset_1('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_366])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_117,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_117])).

tff(c_181,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_194,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_181])).

tff(c_228,plain,(
    ! [B_100,A_101] :
      ( k2_relat_1(B_100) = A_101
      | ~ v2_funct_2(B_100,A_101)
      | ~ v5_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_237,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_228])).

tff(c_246,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_237])).

tff(c_247,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_336,plain,(
    ! [C_125,B_126,A_127] :
      ( v2_funct_2(C_125,B_126)
      | ~ v3_funct_2(C_125,A_127,B_126)
      | ~ v1_funct_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_346,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_336])).

tff(c_351,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_346])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_351])).

tff(c_354,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_393,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_403,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_393])).

tff(c_407,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_403])).

tff(c_422,plain,(
    ! [C_144,A_145,B_146] :
      ( v2_funct_1(C_144)
      | ~ v3_funct_2(C_144,A_145,B_146)
      | ~ v1_funct_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_432,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_422])).

tff(c_437,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_432])).

tff(c_742,plain,(
    ! [A_192,B_193] :
      ( m1_subset_1(k2_funct_2(A_192,B_193),k1_zfmisc_1(k2_zfmisc_1(A_192,A_192)))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_zfmisc_1(A_192,A_192)))
      | ~ v3_funct_2(B_193,A_192,A_192)
      | ~ v1_funct_2(B_193,A_192,A_192)
      | ~ v1_funct_1(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_786,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_742])).

tff(c_803,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_786])).

tff(c_633,plain,(
    ! [A_188,B_189,C_190] :
      ( r2_hidden('#skF_1'(A_188,B_189,C_190),A_188)
      | r2_relset_1(A_188,A_188,B_189,C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188)))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_643,plain,(
    ! [B_189] :
      ( r2_hidden('#skF_1'('#skF_2',B_189,'#skF_3'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_2',B_189,'#skF_3')
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_68,c_633])).

tff(c_844,plain,
    ( r2_hidden('#skF_1'('#skF_2',k2_funct_1('#skF_3'),'#skF_3'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_803,c_643])).

tff(c_871,plain,(
    r2_relset_1('#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_844])).

tff(c_949,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_871,c_26])).

tff(c_952,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_803,c_68,c_949])).

tff(c_644,plain,(
    ! [B_191] :
      ( r2_hidden('#skF_1'('#skF_2',B_191,'#skF_3'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_2',B_191,'#skF_3')
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_68,c_633])).

tff(c_656,plain,
    ( r2_hidden('#skF_1'('#skF_2',k6_partfun1('#skF_2'),'#skF_3'),'#skF_2')
    | r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_644])).

tff(c_660,plain,(
    r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_656])).

tff(c_662,plain,
    ( k6_partfun1('#skF_2') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_660,c_26])).

tff(c_665,plain,(
    k6_partfun1('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_68,c_662])).

tff(c_1044,plain,(
    ! [B_210,C_211,A_212] :
      ( k6_partfun1(B_210) = k5_relat_1(k2_funct_1(C_211),C_211)
      | k1_xboole_0 = B_210
      | ~ v2_funct_1(C_211)
      | k2_relset_1(A_212,B_210,C_211) != B_210
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_212,B_210)))
      | ~ v1_funct_2(C_211,A_212,B_210)
      | ~ v1_funct_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1053,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1044])).

tff(c_1060,plain,
    ( k5_relat_1('#skF_3','#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_407,c_437,c_952,c_665,c_1053])).

tff(c_1061,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1060])).

tff(c_1063,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_2])).

tff(c_1035,plain,(
    ! [A_209] :
      ( r2_hidden('#skF_1'('#skF_2',A_209,'#skF_3'),'#skF_2')
      | r2_relset_1('#skF_2','#skF_2',A_209,'#skF_3')
      | ~ r1_tarski(A_209,k2_zfmisc_1('#skF_2','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12,c_644])).

tff(c_214,plain,(
    ! [C_91,B_92,A_93] :
      ( ~ v1_xboole_0(C_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(C_91))
      | ~ r2_hidden(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_222,plain,(
    ! [B_4,A_93,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_93,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_214])).

tff(c_1038,plain,(
    ! [B_4,A_209] :
      ( ~ v1_xboole_0(B_4)
      | ~ r1_tarski('#skF_2',B_4)
      | r2_relset_1('#skF_2','#skF_2',A_209,'#skF_3')
      | ~ r1_tarski(A_209,k2_zfmisc_1('#skF_2','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1035,c_222])).

tff(c_1151,plain,(
    ! [B_227] :
      ( ~ v1_xboole_0(B_227)
      | ~ r1_tarski('#skF_2',B_227) ) ),
    inference(splitLeft,[status(thm)],[c_1038])).

tff(c_1155,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1151])).

tff(c_1159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1155])).

tff(c_1161,plain,(
    ! [A_228] :
      ( r2_relset_1('#skF_2','#skF_2',A_228,'#skF_3')
      | ~ r1_tarski(A_228,k2_zfmisc_1('#skF_2','#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_1038])).

tff(c_1177,plain,(
    r2_relset_1('#skF_2','#skF_2',k2_zfmisc_1('#skF_2','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1161])).

tff(c_1179,plain,
    ( k2_zfmisc_1('#skF_2','#skF_2') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k2_zfmisc_1('#skF_2','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1177,c_26])).

tff(c_1182,plain,
    ( k2_zfmisc_1('#skF_2','#skF_2') = '#skF_3'
    | ~ m1_subset_1(k2_zfmisc_1('#skF_2','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1179])).

tff(c_1183,plain,(
    ~ m1_subset_1(k2_zfmisc_1('#skF_2','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1182])).

tff(c_1186,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_2'),k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_1183])).

tff(c_1190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1186])).

tff(c_1191,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1182])).

tff(c_90,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_102,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_90])).

tff(c_104,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,
    ( k2_zfmisc_1('#skF_2','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_104])).

tff(c_212,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_1281,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_212])).

tff(c_1287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1281])).

tff(c_1288,plain,(
    k5_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_1017,plain,(
    ! [A_206,D_204,B_205,F_207,E_203,C_208] :
      ( k1_partfun1(A_206,B_205,C_208,D_204,E_203,F_207) = k5_relat_1(E_203,F_207)
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(C_208,D_204)))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205)))
      | ~ v1_funct_1(E_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1026,plain,(
    ! [A_206,B_205,E_203] :
      ( k1_partfun1(A_206,B_205,'#skF_2','#skF_2',E_203,'#skF_3') = k5_relat_1(E_203,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205)))
      | ~ v1_funct_1(E_203) ) ),
    inference(resolution,[status(thm)],[c_68,c_1017])).

tff(c_1294,plain,(
    ! [A_235,B_236,E_237] :
      ( k1_partfun1(A_235,B_236,'#skF_2','#skF_2',E_237,'#skF_3') = k5_relat_1(E_237,'#skF_3')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1026])).

tff(c_1307,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_3') = k5_relat_1('#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1294])).

tff(c_1313,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1288,c_1307])).

tff(c_66,plain,
    ( ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2'))
    | ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_89,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_567,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_89])).

tff(c_667,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_567])).

tff(c_962,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_667])).

tff(c_1314,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1313,c_962])).

tff(c_1318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_1314])).

tff(c_1319,plain,(
    r2_hidden('#skF_1'('#skF_2',k2_funct_1('#skF_3'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_844])).

tff(c_1465,plain,(
    ! [B_253] :
      ( ~ v1_xboole_0(B_253)
      | ~ r1_tarski('#skF_2',B_253) ) ),
    inference(resolution,[status(thm)],[c_1319,c_222])).

tff(c_1470,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1465])).

tff(c_1490,plain,(
    ! [B_254,C_255,A_256] :
      ( k6_partfun1(B_254) = k5_relat_1(k2_funct_1(C_255),C_255)
      | k1_xboole_0 = B_254
      | ~ v2_funct_1(C_255)
      | k2_relset_1(A_256,B_254,C_255) != B_254
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_254)))
      | ~ v1_funct_2(C_255,A_256,B_254)
      | ~ v1_funct_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1501,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1490])).

tff(c_1511,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_407,c_437,c_665,c_1501])).

tff(c_1516,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1511])).

tff(c_1518,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1516,c_2])).

tff(c_1520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1470,c_1518])).

tff(c_1522,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1511])).

tff(c_1620,plain,(
    ! [A_258,C_259,B_260] :
      ( k6_partfun1(A_258) = k5_relat_1(C_259,k2_funct_1(C_259))
      | k1_xboole_0 = B_260
      | ~ v2_funct_1(C_259)
      | k2_relset_1(A_258,B_260,C_259) != B_260
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_258,B_260)))
      | ~ v1_funct_2(C_259,A_258,B_260)
      | ~ v1_funct_1(C_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1633,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1620])).

tff(c_1648,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_407,c_437,c_665,c_1633])).

tff(c_1649,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1522,c_1648])).

tff(c_1441,plain,(
    ! [C_252,B_249,A_250,D_248,F_251,E_247] :
      ( k1_partfun1(A_250,B_249,C_252,D_248,E_247,F_251) = k5_relat_1(E_247,F_251)
      | ~ m1_subset_1(F_251,k1_zfmisc_1(k2_zfmisc_1(C_252,D_248)))
      | ~ v1_funct_1(F_251)
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249)))
      | ~ v1_funct_1(E_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1443,plain,(
    ! [A_250,B_249,E_247] :
      ( k1_partfun1(A_250,B_249,'#skF_2','#skF_2',E_247,k2_funct_1('#skF_3')) = k5_relat_1(E_247,k2_funct_1('#skF_3'))
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_247,k1_zfmisc_1(k2_zfmisc_1(A_250,B_249)))
      | ~ v1_funct_1(E_247) ) ),
    inference(resolution,[status(thm)],[c_803,c_1441])).

tff(c_3673,plain,(
    ! [A_478,B_479,E_480] :
      ( k1_partfun1(A_478,B_479,'#skF_2','#skF_2',E_480,k2_funct_1('#skF_3')) = k5_relat_1(E_480,k2_funct_1('#skF_3'))
      | ~ m1_subset_1(E_480,k1_zfmisc_1(k2_zfmisc_1(A_478,B_479)))
      | ~ v1_funct_1(E_480) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_1443])).

tff(c_3695,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3673])).

tff(c_3705,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1649,c_3695])).

tff(c_3734,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3705,c_667])).

tff(c_3739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_3734])).

tff(c_3740,plain,(
    r2_hidden('#skF_1'('#skF_2',k6_partfun1('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_656])).

tff(c_3749,plain,(
    ! [B_488] :
      ( ~ v1_xboole_0(B_488)
      | ~ r1_tarski('#skF_2',B_488) ) ),
    inference(resolution,[status(thm)],[c_3740,c_222])).

tff(c_3754,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_3749])).

tff(c_4460,plain,(
    ! [A_541,C_542,B_543] :
      ( k6_partfun1(A_541) = k5_relat_1(C_542,k2_funct_1(C_542))
      | k1_xboole_0 = B_543
      | ~ v2_funct_1(C_542)
      | k2_relset_1(A_541,B_543,C_542) != B_543
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_541,B_543)))
      | ~ v1_funct_2(C_542,A_541,B_543)
      | ~ v1_funct_1(C_542) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_4473,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_4460])).

tff(c_4486,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_407,c_437,c_4473])).

tff(c_4493,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4486])).

tff(c_4495,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4493,c_2])).

tff(c_4497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3754,c_4495])).

tff(c_4498,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4486])).

tff(c_3769,plain,(
    ! [A_494,B_495] :
      ( m1_subset_1(k2_funct_2(A_494,B_495),k1_zfmisc_1(k2_zfmisc_1(A_494,A_494)))
      | ~ m1_subset_1(B_495,k1_zfmisc_1(k2_zfmisc_1(A_494,A_494)))
      | ~ v3_funct_2(B_495,A_494,A_494)
      | ~ v1_funct_2(B_495,A_494,A_494)
      | ~ v1_funct_1(B_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3813,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_3769])).

tff(c_3830,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_3813])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3897,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3830,c_10])).

tff(c_4302,plain,(
    ! [D_533,E_532,F_536,A_535,C_537,B_534] :
      ( k1_partfun1(A_535,B_534,C_537,D_533,E_532,F_536) = k5_relat_1(E_532,F_536)
      | ~ m1_subset_1(F_536,k1_zfmisc_1(k2_zfmisc_1(C_537,D_533)))
      | ~ v1_funct_1(F_536)
      | ~ m1_subset_1(E_532,k1_zfmisc_1(k2_zfmisc_1(A_535,B_534)))
      | ~ v1_funct_1(E_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6572,plain,(
    ! [A_730,C_733,D_728,E_732,A_731,B_729] :
      ( k1_partfun1(A_730,B_729,C_733,D_728,E_732,A_731) = k5_relat_1(E_732,A_731)
      | ~ v1_funct_1(A_731)
      | ~ m1_subset_1(E_732,k1_zfmisc_1(k2_zfmisc_1(A_730,B_729)))
      | ~ v1_funct_1(E_732)
      | ~ r1_tarski(A_731,k2_zfmisc_1(C_733,D_728)) ) ),
    inference(resolution,[status(thm)],[c_12,c_4302])).

tff(c_6587,plain,(
    ! [C_733,D_728,A_731] :
      ( k1_partfun1('#skF_2','#skF_2',C_733,D_728,'#skF_3',A_731) = k5_relat_1('#skF_3',A_731)
      | ~ v1_funct_1(A_731)
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski(A_731,k2_zfmisc_1(C_733,D_728)) ) ),
    inference(resolution,[status(thm)],[c_68,c_6572])).

tff(c_6598,plain,(
    ! [C_734,D_735,A_736] :
      ( k1_partfun1('#skF_2','#skF_2',C_734,D_735,'#skF_3',A_736) = k5_relat_1('#skF_3',A_736)
      | ~ v1_funct_1(A_736)
      | ~ r1_tarski(A_736,k2_zfmisc_1(C_734,D_735)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6587])).

tff(c_6607,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3897,c_6598])).

tff(c_6621,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_4498,c_6607])).

tff(c_6629,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6621,c_567])).

tff(c_6634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_6629])).

tff(c_6635,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_6638,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6635,c_68])).

tff(c_7349,plain,(
    ! [A_857,B_858] :
      ( k2_funct_2(A_857,B_858) = k2_funct_1(B_858)
      | ~ m1_subset_1(B_858,k1_zfmisc_1(k2_zfmisc_1(A_857,A_857)))
      | ~ v3_funct_2(B_858,A_857,A_857)
      | ~ v1_funct_2(B_858,A_857,A_857)
      | ~ v1_funct_1(B_858) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_7362,plain,(
    ! [B_859] :
      ( k2_funct_2('#skF_2',B_859) = k2_funct_1(B_859)
      | ~ m1_subset_1(B_859,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_859,'#skF_2','#skF_2')
      | ~ v1_funct_2(B_859,'#skF_2','#skF_2')
      | ~ v1_funct_1(B_859) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_7349])).

tff(c_7368,plain,
    ( k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6638,c_7362])).

tff(c_7376,plain,(
    k2_funct_2('#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_7368])).

tff(c_7305,plain,(
    ! [A_850,B_851] :
      ( v1_funct_1(k2_funct_2(A_850,B_851))
      | ~ m1_subset_1(B_851,k1_zfmisc_1(k2_zfmisc_1(A_850,A_850)))
      | ~ v3_funct_2(B_851,A_850,A_850)
      | ~ v1_funct_2(B_851,A_850,A_850)
      | ~ v1_funct_1(B_851) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_7319,plain,(
    ! [B_853] :
      ( v1_funct_1(k2_funct_2('#skF_2',B_853))
      | ~ m1_subset_1(B_853,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_853,'#skF_2','#skF_2')
      | ~ v1_funct_2(B_853,'#skF_2','#skF_2')
      | ~ v1_funct_1(B_853) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_7305])).

tff(c_7325,plain,
    ( v1_funct_1(k2_funct_2('#skF_2','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6638,c_7319])).

tff(c_7333,plain,(
    v1_funct_1(k2_funct_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_7325])).

tff(c_7378,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7376,c_7333])).

tff(c_6774,plain,(
    ! [B_754,A_755] :
      ( k2_relat_1(B_754) = A_755
      | ~ v2_funct_2(B_754,A_755)
      | ~ v5_relat_1(B_754,A_755)
      | ~ v1_relat_1(B_754) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6786,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_6774])).

tff(c_6796,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6786])).

tff(c_6797,plain,(
    ~ v2_funct_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6796])).

tff(c_6964,plain,(
    ! [C_788,B_789,A_790] :
      ( v2_funct_2(C_788,B_789)
      | ~ v3_funct_2(C_788,A_790,B_789)
      | ~ v1_funct_1(C_788)
      | ~ m1_subset_1(C_788,k1_zfmisc_1(k2_zfmisc_1(A_790,B_789))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6998,plain,(
    ! [C_796] :
      ( v2_funct_2(C_796,'#skF_2')
      | ~ v3_funct_2(C_796,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_796)
      | ~ m1_subset_1(C_796,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_6964])).

tff(c_7004,plain,
    ( v2_funct_2('#skF_3','#skF_2')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6638,c_6998])).

tff(c_7012,plain,(
    v2_funct_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_7004])).

tff(c_7014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6797,c_7012])).

tff(c_7015,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6796])).

tff(c_7090,plain,(
    ! [A_813,B_814,C_815] :
      ( k2_relset_1(A_813,B_814,C_815) = k2_relat_1(C_815)
      | ~ m1_subset_1(C_815,k1_zfmisc_1(k2_zfmisc_1(A_813,B_814))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7125,plain,(
    ! [C_820] :
      ( k2_relset_1('#skF_2','#skF_2',C_820) = k2_relat_1(C_820)
      | ~ m1_subset_1(C_820,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_7090])).

tff(c_7131,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6638,c_7125])).

tff(c_7139,plain,(
    k2_relset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7015,c_7131])).

tff(c_7103,plain,(
    ! [C_816,A_817,B_818] :
      ( v2_funct_1(C_816)
      | ~ v3_funct_2(C_816,A_817,B_818)
      | ~ v1_funct_1(C_816)
      | ~ m1_subset_1(C_816,k1_zfmisc_1(k2_zfmisc_1(A_817,B_818))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7145,plain,(
    ! [C_821] :
      ( v2_funct_1(C_821)
      | ~ v3_funct_2(C_821,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_821)
      | ~ m1_subset_1(C_821,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_7103])).

tff(c_7151,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6638,c_7145])).

tff(c_7159,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_7151])).

tff(c_7428,plain,(
    ! [A_868,B_869] :
      ( v3_funct_2(k2_funct_2(A_868,B_869),A_868,A_868)
      | ~ m1_subset_1(B_869,k1_zfmisc_1(k2_zfmisc_1(A_868,A_868)))
      | ~ v3_funct_2(B_869,A_868,A_868)
      | ~ v1_funct_2(B_869,A_868,A_868)
      | ~ v1_funct_1(B_869) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_7454,plain,(
    ! [B_871] :
      ( v3_funct_2(k2_funct_2('#skF_2',B_871),'#skF_2','#skF_2')
      | ~ m1_subset_1(B_871,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_871,'#skF_2','#skF_2')
      | ~ v1_funct_2(B_871,'#skF_2','#skF_2')
      | ~ v1_funct_1(B_871) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_7428])).

tff(c_7466,plain,
    ( v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7376,c_7454])).

tff(c_7471,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_6638,c_7466])).

tff(c_7160,plain,(
    ! [A_3] :
      ( v2_funct_1(A_3)
      | ~ v3_funct_2(A_3,'#skF_2','#skF_2')
      | ~ v1_funct_1(A_3)
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_7145])).

tff(c_7480,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7471,c_7160])).

tff(c_7489,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7378,c_7480])).

tff(c_7490,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7489])).

tff(c_7759,plain,(
    ! [A_903,B_904] :
      ( m1_subset_1(k2_funct_2(A_903,B_904),k1_zfmisc_1(k2_zfmisc_1(A_903,A_903)))
      | ~ m1_subset_1(B_904,k1_zfmisc_1(k2_zfmisc_1(A_903,A_903)))
      | ~ v3_funct_2(B_904,A_903,A_903)
      | ~ v1_funct_2(B_904,A_903,A_903)
      | ~ v1_funct_1(B_904) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_7806,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7376,c_7759])).

tff(c_7828,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_6638,c_6635,c_6635,c_7806])).

tff(c_7862,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7828,c_10])).

tff(c_7887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7490,c_7862])).

tff(c_7889,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_7489])).

tff(c_7389,plain,(
    ! [A_860,B_861] :
      ( v1_funct_2(k2_funct_2(A_860,B_861),A_860,A_860)
      | ~ m1_subset_1(B_861,k1_zfmisc_1(k2_zfmisc_1(A_860,A_860)))
      | ~ v3_funct_2(B_861,A_860,A_860)
      | ~ v1_funct_2(B_861,A_860,A_860)
      | ~ v1_funct_1(B_861) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_7400,plain,(
    ! [B_862] :
      ( v1_funct_2(k2_funct_2('#skF_2',B_862),'#skF_2','#skF_2')
      | ~ m1_subset_1(B_862,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_862,'#skF_2','#skF_2')
      | ~ v1_funct_2(B_862,'#skF_2','#skF_2')
      | ~ v1_funct_1(B_862) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_7389])).

tff(c_7403,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7376,c_7400])).

tff(c_7405,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_6638,c_7403])).

tff(c_7377,plain,(
    ! [A_3] :
      ( k2_funct_2('#skF_2',A_3) = k2_funct_1(A_3)
      | ~ v3_funct_2(A_3,'#skF_2','#skF_2')
      | ~ v1_funct_2(A_3,'#skF_2','#skF_2')
      | ~ v1_funct_1(A_3)
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_7362])).

tff(c_7474,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7471,c_7377])).

tff(c_7483,plain,
    ( k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7378,c_7405,c_7474])).

tff(c_7936,plain,(
    k2_funct_2('#skF_2',k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7889,c_7483])).

tff(c_7391,plain,(
    ! [B_861] :
      ( v1_funct_2(k2_funct_2('#skF_2',B_861),'#skF_2','#skF_2')
      | ~ m1_subset_1(B_861,k1_zfmisc_1('#skF_3'))
      | ~ v3_funct_2(B_861,'#skF_2','#skF_2')
      | ~ v1_funct_2(B_861,'#skF_2','#skF_2')
      | ~ v1_funct_1(B_861) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_7389])).

tff(c_7943,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7936,c_7391])).

tff(c_7952,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),'#skF_2','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7378,c_7405,c_7471,c_7943])).

tff(c_7956,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7952])).

tff(c_7963,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_7956])).

tff(c_7967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7889,c_7963])).

tff(c_7969,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7952])).

tff(c_8463,plain,(
    ! [D_936,C_940,A_938,E_935,F_939,B_937] :
      ( k1_partfun1(A_938,B_937,C_940,D_936,E_935,F_939) = k5_relat_1(E_935,F_939)
      | ~ m1_subset_1(F_939,k1_zfmisc_1(k2_zfmisc_1(C_940,D_936)))
      | ~ v1_funct_1(F_939)
      | ~ m1_subset_1(E_935,k1_zfmisc_1(k2_zfmisc_1(A_938,B_937)))
      | ~ v1_funct_1(E_935) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10767,plain,(
    ! [B_1075,A_1077,E_1076,A_1078,C_1074,D_1073] :
      ( k1_partfun1(A_1078,B_1075,C_1074,D_1073,E_1076,A_1077) = k5_relat_1(E_1076,A_1077)
      | ~ v1_funct_1(A_1077)
      | ~ m1_subset_1(E_1076,k1_zfmisc_1(k2_zfmisc_1(A_1078,B_1075)))
      | ~ v1_funct_1(E_1076)
      | ~ r1_tarski(A_1077,k2_zfmisc_1(C_1074,D_1073)) ) ),
    inference(resolution,[status(thm)],[c_12,c_8463])).

tff(c_10790,plain,(
    ! [C_1079,D_1080,E_1081,A_1082] :
      ( k1_partfun1('#skF_2','#skF_2',C_1079,D_1080,E_1081,A_1082) = k5_relat_1(E_1081,A_1082)
      | ~ v1_funct_1(A_1082)
      | ~ m1_subset_1(E_1081,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_1(E_1081)
      | ~ r1_tarski(A_1082,k2_zfmisc_1(C_1079,D_1080)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_10767])).

tff(c_10816,plain,(
    ! [C_1079,D_1080,A_1082] :
      ( k1_partfun1('#skF_2','#skF_2',C_1079,D_1080,'#skF_3',A_1082) = k5_relat_1('#skF_3',A_1082)
      | ~ v1_funct_1(A_1082)
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski(A_1082,k2_zfmisc_1(C_1079,D_1080)) ) ),
    inference(resolution,[status(thm)],[c_6638,c_10790])).

tff(c_10884,plain,(
    ! [C_1089,D_1090,A_1091] :
      ( k1_partfun1('#skF_2','#skF_2',C_1089,D_1090,'#skF_3',A_1091) = k5_relat_1('#skF_3',A_1091)
      | ~ v1_funct_1(A_1091)
      | ~ r1_tarski(A_1091,k2_zfmisc_1(C_1089,D_1090)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10816])).

tff(c_10901,plain,(
    ! [A_1092] :
      ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',A_1092) = k5_relat_1('#skF_3',A_1092)
      | ~ v1_funct_1(A_1092)
      | ~ r1_tarski(A_1092,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_10884])).

tff(c_10931,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7889,c_10901])).

tff(c_10968,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7378,c_10931])).

tff(c_8768,plain,(
    ! [C_957,B_956,E_955,F_954,A_952,D_953] :
      ( m1_subset_1(k1_partfun1(A_952,B_956,C_957,D_953,E_955,F_954),k1_zfmisc_1(k2_zfmisc_1(A_952,D_953)))
      | ~ m1_subset_1(F_954,k1_zfmisc_1(k2_zfmisc_1(C_957,D_953)))
      | ~ v1_funct_1(F_954)
      | ~ m1_subset_1(E_955,k1_zfmisc_1(k2_zfmisc_1(A_952,B_956)))
      | ~ v1_funct_1(E_955) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8824,plain,(
    ! [B_956,C_957,E_955,F_954] :
      ( m1_subset_1(k1_partfun1('#skF_2',B_956,C_957,'#skF_2',E_955,F_954),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(F_954,k1_zfmisc_1(k2_zfmisc_1(C_957,'#skF_2')))
      | ~ v1_funct_1(F_954)
      | ~ m1_subset_1(E_955,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_956)))
      | ~ v1_funct_1(E_955) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_8768])).

tff(c_10980,plain,
    ( m1_subset_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10968,c_8824])).

tff(c_10992,plain,(
    m1_subset_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6638,c_6635,c_7378,c_7969,c_6635,c_10980])).

tff(c_8569,plain,(
    ! [B_942,C_943,A_944] :
      ( k6_partfun1(B_942) = k5_relat_1(k2_funct_1(C_943),C_943)
      | k1_xboole_0 = B_942
      | ~ v2_funct_1(C_943)
      | k2_relset_1(A_944,B_942,C_943) != B_942
      | ~ m1_subset_1(C_943,k1_zfmisc_1(k2_zfmisc_1(A_944,B_942)))
      | ~ v1_funct_2(C_943,A_944,B_942)
      | ~ v1_funct_1(C_943) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8573,plain,(
    ! [C_943] :
      ( k5_relat_1(k2_funct_1(C_943),C_943) = k6_partfun1('#skF_2')
      | k1_xboole_0 = '#skF_2'
      | ~ v2_funct_1(C_943)
      | k2_relset_1('#skF_2','#skF_2',C_943) != '#skF_2'
      | ~ m1_subset_1(C_943,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_943,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_943) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_8569])).

tff(c_10011,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8573])).

tff(c_10014,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10011,c_2])).

tff(c_7924,plain,(
    ! [A_905,B_906,C_907] :
      ( r2_hidden('#skF_1'(A_905,B_906,C_907),A_905)
      | r2_relset_1(A_905,A_905,B_906,C_907)
      | ~ m1_subset_1(C_907,k1_zfmisc_1(k2_zfmisc_1(A_905,A_905)))
      | ~ m1_subset_1(B_906,k1_zfmisc_1(k2_zfmisc_1(A_905,A_905))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8930,plain,(
    ! [A_966,B_967] :
      ( r2_hidden('#skF_1'(A_966,B_967,k6_partfun1(A_966)),A_966)
      | r2_relset_1(A_966,A_966,B_967,k6_partfun1(A_966))
      | ~ m1_subset_1(B_967,k1_zfmisc_1(k2_zfmisc_1(A_966,A_966))) ) ),
    inference(resolution,[status(thm)],[c_75,c_7924])).

tff(c_6704,plain,(
    ! [C_740,B_741,A_742] :
      ( ~ v1_xboole_0(C_740)
      | ~ m1_subset_1(B_741,k1_zfmisc_1(C_740))
      | ~ r2_hidden(A_742,B_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6716,plain,(
    ! [B_4,A_742,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_742,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_6704])).

tff(c_15580,plain,(
    ! [B_1271,A_1272,B_1273] :
      ( ~ v1_xboole_0(B_1271)
      | ~ r1_tarski(A_1272,B_1271)
      | r2_relset_1(A_1272,A_1272,B_1273,k6_partfun1(A_1272))
      | ~ m1_subset_1(B_1273,k1_zfmisc_1(k2_zfmisc_1(A_1272,A_1272))) ) ),
    inference(resolution,[status(thm)],[c_8930,c_6716])).

tff(c_15656,plain,(
    ! [B_1274,B_1275] :
      ( ~ v1_xboole_0(B_1274)
      | r2_relset_1(B_1274,B_1274,B_1275,k6_partfun1(B_1274))
      | ~ m1_subset_1(B_1275,k1_zfmisc_1(k2_zfmisc_1(B_1274,B_1274))) ) ),
    inference(resolution,[status(thm)],[c_8,c_15580])).

tff(c_15663,plain,(
    ! [B_1275] :
      ( ~ v1_xboole_0('#skF_2')
      | r2_relset_1('#skF_2','#skF_2',B_1275,k6_partfun1('#skF_2'))
      | ~ m1_subset_1(B_1275,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_15656])).

tff(c_15692,plain,(
    ! [B_1282] :
      ( r2_relset_1('#skF_2','#skF_2',B_1282,k6_partfun1('#skF_2'))
      | ~ m1_subset_1(B_1282,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10014,c_15663])).

tff(c_7379,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7376,c_89])).

tff(c_10973,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10968,c_7379])).

tff(c_15695,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15692,c_10973])).

tff(c_15701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10992,c_15695])).

tff(c_15703,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8573])).

tff(c_8633,plain,(
    ! [A_946,C_947,B_948] :
      ( k6_partfun1(A_946) = k5_relat_1(C_947,k2_funct_1(C_947))
      | k1_xboole_0 = B_948
      | ~ v2_funct_1(C_947)
      | k2_relset_1(A_946,B_948,C_947) != B_948
      | ~ m1_subset_1(C_947,k1_zfmisc_1(k2_zfmisc_1(A_946,B_948)))
      | ~ v1_funct_2(C_947,A_946,B_948)
      | ~ v1_funct_1(C_947) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8637,plain,(
    ! [C_947] :
      ( k5_relat_1(C_947,k2_funct_1(C_947)) = k6_partfun1('#skF_2')
      | k1_xboole_0 = '#skF_2'
      | ~ v2_funct_1(C_947)
      | k2_relset_1('#skF_2','#skF_2',C_947) != '#skF_2'
      | ~ m1_subset_1(C_947,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_947,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_947) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_8633])).

tff(c_15979,plain,(
    ! [C_1309] :
      ( k5_relat_1(C_1309,k2_funct_1(C_1309)) = k6_partfun1('#skF_2')
      | ~ v2_funct_1(C_1309)
      | k2_relset_1('#skF_2','#skF_2',C_1309) != '#skF_2'
      | ~ m1_subset_1(C_1309,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_2(C_1309,'#skF_2','#skF_2')
      | ~ v1_funct_1(C_1309) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15703,c_8637])).

tff(c_15999,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6638,c_15979])).

tff(c_16031,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_7139,c_7159,c_15999])).

tff(c_16055,plain,(
    ! [B_1314,E_1315,C_1313,A_1316,A_1317,D_1312] :
      ( k1_partfun1(A_1317,B_1314,C_1313,D_1312,E_1315,A_1316) = k5_relat_1(E_1315,A_1316)
      | ~ v1_funct_1(A_1316)
      | ~ m1_subset_1(E_1315,k1_zfmisc_1(k2_zfmisc_1(A_1317,B_1314)))
      | ~ v1_funct_1(E_1315)
      | ~ r1_tarski(A_1316,k2_zfmisc_1(C_1313,D_1312)) ) ),
    inference(resolution,[status(thm)],[c_12,c_8463])).

tff(c_16102,plain,(
    ! [C_1321,D_1322,E_1323,A_1324] :
      ( k1_partfun1('#skF_2','#skF_2',C_1321,D_1322,E_1323,A_1324) = k5_relat_1(E_1323,A_1324)
      | ~ v1_funct_1(A_1324)
      | ~ m1_subset_1(E_1323,k1_zfmisc_1('#skF_3'))
      | ~ v1_funct_1(E_1323)
      | ~ r1_tarski(A_1324,k2_zfmisc_1(C_1321,D_1322)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_16055])).

tff(c_16122,plain,(
    ! [C_1321,D_1322,A_1324] :
      ( k1_partfun1('#skF_2','#skF_2',C_1321,D_1322,'#skF_3',A_1324) = k5_relat_1('#skF_3',A_1324)
      | ~ v1_funct_1(A_1324)
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski(A_1324,k2_zfmisc_1(C_1321,D_1322)) ) ),
    inference(resolution,[status(thm)],[c_6638,c_16102])).

tff(c_16287,plain,(
    ! [C_1326,D_1327,A_1328] :
      ( k1_partfun1('#skF_2','#skF_2',C_1326,D_1327,'#skF_3',A_1328) = k5_relat_1('#skF_3',A_1328)
      | ~ v1_funct_1(A_1328)
      | ~ r1_tarski(A_1328,k2_zfmisc_1(C_1326,D_1327)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16122])).

tff(c_16304,plain,(
    ! [A_1329] :
      ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',A_1329) = k5_relat_1('#skF_3',A_1329)
      | ~ v1_funct_1(A_1329)
      | ~ r1_tarski(A_1329,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6635,c_16287])).

tff(c_16331,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7889,c_16304])).

tff(c_16365,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7378,c_16031,c_16331])).

tff(c_16370,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16365,c_7379])).

tff(c_16373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7042,c_16370])).

tff(c_16375,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_16741,plain,(
    ! [D_1423,C_1424,A_1425,B_1426] :
      ( D_1423 = C_1424
      | ~ r2_relset_1(A_1425,B_1426,C_1424,D_1423)
      | ~ m1_subset_1(D_1423,k1_zfmisc_1(k2_zfmisc_1(A_1425,B_1426)))
      | ~ m1_subset_1(C_1424,k1_zfmisc_1(k2_zfmisc_1(A_1425,B_1426))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16749,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_16375,c_16741])).

tff(c_16762,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')) = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_2('#skF_2','#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_16749])).

tff(c_16895,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16828,c_16828,c_16762])).

tff(c_16896,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_16895])).

tff(c_17868,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_17841,c_16896])).

tff(c_17920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_68,c_16829,c_17102,c_17868])).

tff(c_17921,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_16895])).

tff(c_17998,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3',k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17996,c_17921])).

tff(c_18361,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18350,c_17998])).

tff(c_16374,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_2('#skF_2','#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_16831,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16828,c_16374])).

tff(c_17999,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17996,c_16831])).

tff(c_18360,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2','#skF_3','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18350,c_17999])).

tff(c_18494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16524,c_18361,c_18360])).

tff(c_18495,plain,(
    r2_hidden('#skF_1'('#skF_2',k2_funct_1('#skF_3'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_18236])).

tff(c_16499,plain,(
    ! [C_1362,B_1363,A_1364] :
      ( ~ v1_xboole_0(C_1362)
      | ~ m1_subset_1(B_1363,k1_zfmisc_1(C_1362))
      | ~ r2_hidden(A_1364,B_1363) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16507,plain,(
    ! [B_4,A_1364,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_1364,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_16499])).

tff(c_18643,plain,(
    ! [B_1565] :
      ( ~ v1_xboole_0(B_1565)
      | ~ r1_tarski('#skF_2',B_1565) ) ),
    inference(resolution,[status(thm)],[c_18495,c_16507])).

tff(c_18647,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_18643])).

tff(c_18651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18638,c_18647])).

tff(c_18652,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18630])).

tff(c_18503,plain,(
    ! [D_1556,C_1560,A_1558,B_1557,E_1555,F_1559] :
      ( k1_partfun1(A_1558,B_1557,C_1560,D_1556,E_1555,F_1559) = k5_relat_1(E_1555,F_1559)
      | ~ m1_subset_1(F_1559,k1_zfmisc_1(k2_zfmisc_1(C_1560,D_1556)))
      | ~ v1_funct_1(F_1559)
      | ~ m1_subset_1(E_1555,k1_zfmisc_1(k2_zfmisc_1(A_1558,B_1557)))
      | ~ v1_funct_1(E_1555) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_18514,plain,(
    ! [A_1558,B_1557,E_1555] :
      ( k1_partfun1(A_1558,B_1557,'#skF_2','#skF_2',E_1555,'#skF_3') = k5_relat_1(E_1555,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_1555,k1_zfmisc_1(k2_zfmisc_1(A_1558,B_1557)))
      | ~ v1_funct_1(E_1555) ) ),
    inference(resolution,[status(thm)],[c_68,c_18503])).

tff(c_18692,plain,(
    ! [A_1570,B_1571,E_1572] :
      ( k1_partfun1(A_1570,B_1571,'#skF_2','#skF_2',E_1572,'#skF_3') = k5_relat_1(E_1572,'#skF_3')
      | ~ m1_subset_1(E_1572,k1_zfmisc_1(k2_zfmisc_1(A_1570,B_1571)))
      | ~ v1_funct_1(E_1572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18514])).

tff(c_18695,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18184,c_18692])).

tff(c_18711,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16829,c_18652,c_18695])).

tff(c_19291,plain,(
    ~ r2_relset_1('#skF_2','#skF_2','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18711,c_17999])).

tff(c_19295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16524,c_19291])).

tff(c_19296,plain,(
    r2_hidden('#skF_1'('#skF_2',k6_partfun1('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_17974])).

tff(c_19317,plain,(
    ! [B_1591] :
      ( ~ v1_xboole_0(B_1591)
      | ~ r1_tarski('#skF_2',B_1591) ) ),
    inference(resolution,[status(thm)],[c_19296,c_16507])).

tff(c_19322,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_19317])).

tff(c_19839,plain,(
    ! [B_1624,C_1625,A_1626] :
      ( k6_partfun1(B_1624) = k5_relat_1(k2_funct_1(C_1625),C_1625)
      | k1_xboole_0 = B_1624
      | ~ v2_funct_1(C_1625)
      | k2_relset_1(A_1626,B_1624,C_1625) != B_1624
      | ~ m1_subset_1(C_1625,k1_zfmisc_1(k2_zfmisc_1(A_1626,B_1624)))
      | ~ v1_funct_2(C_1625,A_1626,B_1624)
      | ~ v1_funct_1(C_1625) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_19850,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_2','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_19839])).

tff(c_19860,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_16652,c_16694,c_19850])).

tff(c_19885,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_19860])).

tff(c_19887,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19885,c_2])).

tff(c_19889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19322,c_19887])).

tff(c_19890,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_19860])).

tff(c_19340,plain,(
    ! [A_1596,B_1597] :
      ( m1_subset_1(k2_funct_2(A_1596,B_1597),k1_zfmisc_1(k2_zfmisc_1(A_1596,A_1596)))
      | ~ m1_subset_1(B_1597,k1_zfmisc_1(k2_zfmisc_1(A_1596,A_1596)))
      | ~ v3_funct_2(B_1597,A_1596,A_1596)
      | ~ v1_funct_2(B_1597,A_1596,A_1596)
      | ~ v1_funct_1(B_1597) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_19389,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ v3_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16828,c_19340])).

tff(c_19408,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_19389])).

tff(c_19739,plain,(
    ! [F_1621,D_1618,E_1617,C_1622,B_1619,A_1620] :
      ( k1_partfun1(A_1620,B_1619,C_1622,D_1618,E_1617,F_1621) = k5_relat_1(E_1617,F_1621)
      | ~ m1_subset_1(F_1621,k1_zfmisc_1(k2_zfmisc_1(C_1622,D_1618)))
      | ~ v1_funct_1(F_1621)
      | ~ m1_subset_1(E_1617,k1_zfmisc_1(k2_zfmisc_1(A_1620,B_1619)))
      | ~ v1_funct_1(E_1617) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_19750,plain,(
    ! [A_1620,B_1619,E_1617] :
      ( k1_partfun1(A_1620,B_1619,'#skF_2','#skF_2',E_1617,'#skF_3') = k5_relat_1(E_1617,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_1617,k1_zfmisc_1(k2_zfmisc_1(A_1620,B_1619)))
      | ~ v1_funct_1(E_1617) ) ),
    inference(resolution,[status(thm)],[c_68,c_19739])).

tff(c_19925,plain,(
    ! [A_1630,B_1631,E_1632] :
      ( k1_partfun1(A_1630,B_1631,'#skF_2','#skF_2',E_1632,'#skF_3') = k5_relat_1(E_1632,'#skF_3')
      | ~ m1_subset_1(E_1632,k1_zfmisc_1(k2_zfmisc_1(A_1630,B_1631)))
      | ~ v1_funct_1(E_1632) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_19750])).

tff(c_19928,plain,
    ( k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_19408,c_19925])).

tff(c_19944,plain,(
    k1_partfun1('#skF_2','#skF_2','#skF_2','#skF_2',k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16829,c_19890,c_19928])).

tff(c_20542,plain,(
    ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19944,c_16831])).

tff(c_20545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16522,c_20542])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 17:25:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.57/5.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.77/5.74  
% 12.77/5.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.77/5.74  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k11_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 12.77/5.74  
% 12.77/5.74  %Foreground sorts:
% 12.77/5.74  
% 12.77/5.74  
% 12.77/5.74  %Background operators:
% 12.77/5.74  
% 12.77/5.74  
% 12.77/5.74  %Foreground operators:
% 12.77/5.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.77/5.74  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.77/5.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.77/5.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.77/5.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.77/5.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.77/5.74  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.77/5.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.77/5.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.77/5.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.77/5.74  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 12.77/5.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.77/5.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.77/5.74  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.77/5.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.77/5.74  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 12.77/5.74  tff('#skF_2', type, '#skF_2': $i).
% 12.77/5.74  tff('#skF_3', type, '#skF_3': $i).
% 12.77/5.74  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 12.77/5.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.77/5.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.77/5.74  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.77/5.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.77/5.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.77/5.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.77/5.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.77/5.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.77/5.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.77/5.74  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 12.77/5.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.77/5.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.77/5.74  
% 12.77/5.78  tff(f_149, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.77/5.78  tff(f_67, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 12.77/5.78  tff(f_65, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.77/5.78  tff(f_178, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 12.77/5.78  tff(f_147, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 12.77/5.78  tff(f_127, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 12.77/5.78  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.77/5.78  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.77/5.78  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.77/5.78  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 12.77/5.78  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 12.77/5.78  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.77/5.78  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relset_1)).
% 12.77/5.78  tff(f_165, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 12.77/5.78  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.77/5.78  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.77/5.78  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.77/5.78  tff(f_43, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 12.77/5.78  tff(f_137, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.77/5.78  tff(c_60, plain, (![A_50]: (k6_relat_1(A_50)=k6_partfun1(A_50))), inference(cnfTransformation, [status(thm)], [f_149])).
% 12.77/5.78  tff(c_28, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.77/5.78  tff(c_75, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_28])).
% 12.77/5.78  tff(c_16514, plain, (![A_1371, B_1372, D_1373]: (r2_relset_1(A_1371, B_1372, D_1373, D_1373) | ~m1_subset_1(D_1373, k1_zfmisc_1(k2_zfmisc_1(A_1371, B_1372))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.77/5.78  tff(c_16522, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_75, c_16514])).
% 12.77/5.78  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.77/5.78  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.77/5.78  tff(c_70, plain, (v3_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.77/5.78  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.77/5.78  tff(c_16813, plain, (![A_1439, B_1440]: (k2_funct_2(A_1439, B_1440)=k2_funct_1(B_1440) | ~m1_subset_1(B_1440, k1_zfmisc_1(k2_zfmisc_1(A_1439, A_1439))) | ~v3_funct_2(B_1440, A_1439, A_1439) | ~v1_funct_2(B_1440, A_1439, A_1439) | ~v1_funct_1(B_1440))), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.77/5.78  tff(c_16823, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_16813])).
% 12.77/5.78  tff(c_16828, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_16823])).
% 12.77/5.78  tff(c_16797, plain, (![A_1437, B_1438]: (v1_funct_1(k2_funct_2(A_1437, B_1438)) | ~m1_subset_1(B_1438, k1_zfmisc_1(k2_zfmisc_1(A_1437, A_1437))) | ~v3_funct_2(B_1438, A_1437, A_1437) | ~v1_funct_2(B_1438, A_1437, A_1437) | ~v1_funct_1(B_1438))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_16807, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_16797])).
% 12.77/5.78  tff(c_16812, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_16807])).
% 12.77/5.78  tff(c_16829, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16828, c_16812])).
% 12.77/5.78  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.77/5.78  tff(c_16524, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_16514])).
% 12.77/5.78  tff(c_16389, plain, (![C_1332, A_1333, B_1334]: (v1_relat_1(C_1332) | ~m1_subset_1(C_1332, k1_zfmisc_1(k2_zfmisc_1(A_1333, B_1334))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.77/5.78  tff(c_16402, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_16389])).
% 12.77/5.78  tff(c_16435, plain, (![C_1344, B_1345, A_1346]: (v5_relat_1(C_1344, B_1345) | ~m1_subset_1(C_1344, k1_zfmisc_1(k2_zfmisc_1(A_1346, B_1345))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.77/5.78  tff(c_16448, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_16435])).
% 12.77/5.78  tff(c_16525, plain, (![B_1374, A_1375]: (k2_relat_1(B_1374)=A_1375 | ~v2_funct_2(B_1374, A_1375) | ~v5_relat_1(B_1374, A_1375) | ~v1_relat_1(B_1374))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.77/5.78  tff(c_16534, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16448, c_16525])).
% 12.77/5.78  tff(c_16543, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16402, c_16534])).
% 12.77/5.78  tff(c_16544, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_16543])).
% 12.77/5.78  tff(c_16606, plain, (![C_1393, B_1394, A_1395]: (v2_funct_2(C_1393, B_1394) | ~v3_funct_2(C_1393, A_1395, B_1394) | ~v1_funct_1(C_1393) | ~m1_subset_1(C_1393, k1_zfmisc_1(k2_zfmisc_1(A_1395, B_1394))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.77/5.78  tff(c_16616, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_16606])).
% 12.77/5.78  tff(c_16621, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_16616])).
% 12.77/5.78  tff(c_16623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16544, c_16621])).
% 12.77/5.78  tff(c_16624, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_16543])).
% 12.77/5.78  tff(c_16638, plain, (![A_1398, B_1399, C_1400]: (k2_relset_1(A_1398, B_1399, C_1400)=k2_relat_1(C_1400) | ~m1_subset_1(C_1400, k1_zfmisc_1(k2_zfmisc_1(A_1398, B_1399))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.77/5.78  tff(c_16648, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_16638])).
% 12.77/5.78  tff(c_16652, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16624, c_16648])).
% 12.77/5.78  tff(c_16679, plain, (![C_1405, A_1406, B_1407]: (v2_funct_1(C_1405) | ~v3_funct_2(C_1405, A_1406, B_1407) | ~v1_funct_1(C_1405) | ~m1_subset_1(C_1405, k1_zfmisc_1(k2_zfmisc_1(A_1406, B_1407))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.77/5.78  tff(c_16689, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_16679])).
% 12.77/5.78  tff(c_16694, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_16689])).
% 12.77/5.78  tff(c_17951, plain, (![A_1520, B_1521, C_1522]: (r2_hidden('#skF_1'(A_1520, B_1521, C_1522), A_1520) | r2_relset_1(A_1520, A_1520, B_1521, C_1522) | ~m1_subset_1(C_1522, k1_zfmisc_1(k2_zfmisc_1(A_1520, A_1520))) | ~m1_subset_1(B_1521, k1_zfmisc_1(k2_zfmisc_1(A_1520, A_1520))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.77/5.78  tff(c_17962, plain, (![B_1523]: (r2_hidden('#skF_1'('#skF_2', B_1523, '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', B_1523, '#skF_3') | ~m1_subset_1(B_1523, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))))), inference(resolution, [status(thm)], [c_68, c_17951])).
% 12.77/5.78  tff(c_17974, plain, (r2_hidden('#skF_1'('#skF_2', k6_partfun1('#skF_2'), '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_75, c_17962])).
% 12.77/5.78  tff(c_17991, plain, (r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_17974])).
% 12.77/5.78  tff(c_26, plain, (![D_20, C_19, A_17, B_18]: (D_20=C_19 | ~r2_relset_1(A_17, B_18, C_19, D_20) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.77/5.78  tff(c_17993, plain, (k6_partfun1('#skF_2')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_17991, c_26])).
% 12.77/5.78  tff(c_17996, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_68, c_17993])).
% 12.77/5.78  tff(c_18609, plain, (![B_1562, C_1563, A_1564]: (k6_partfun1(B_1562)=k5_relat_1(k2_funct_1(C_1563), C_1563) | k1_xboole_0=B_1562 | ~v2_funct_1(C_1563) | k2_relset_1(A_1564, B_1562, C_1563)!=B_1562 | ~m1_subset_1(C_1563, k1_zfmisc_1(k2_zfmisc_1(A_1564, B_1562))) | ~v1_funct_2(C_1563, A_1564, B_1562) | ~v1_funct_1(C_1563))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.77/5.78  tff(c_18620, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_18609])).
% 12.77/5.78  tff(c_18630, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_16652, c_16694, c_17996, c_18620])).
% 12.77/5.78  tff(c_18636, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_18630])).
% 12.77/5.78  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.77/5.78  tff(c_18638, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18636, c_2])).
% 12.77/5.78  tff(c_18116, plain, (![A_1537, B_1538]: (m1_subset_1(k2_funct_2(A_1537, B_1538), k1_zfmisc_1(k2_zfmisc_1(A_1537, A_1537))) | ~m1_subset_1(B_1538, k1_zfmisc_1(k2_zfmisc_1(A_1537, A_1537))) | ~v3_funct_2(B_1538, A_1537, A_1537) | ~v1_funct_2(B_1538, A_1537, A_1537) | ~v1_funct_1(B_1538))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_18165, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16828, c_18116])).
% 12.77/5.78  tff(c_18184, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_18165])).
% 12.77/5.78  tff(c_17961, plain, (![B_1521]: (r2_hidden('#skF_1'('#skF_2', B_1521, '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', B_1521, '#skF_3') | ~m1_subset_1(B_1521, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))))), inference(resolution, [status(thm)], [c_68, c_17951])).
% 12.77/5.78  tff(c_18236, plain, (r2_hidden('#skF_1'('#skF_2', k2_funct_1('#skF_3'), '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_18184, c_17961])).
% 12.77/5.78  tff(c_18263, plain, (r2_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_18236])).
% 12.77/5.78  tff(c_18347, plain, (k2_funct_1('#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_18263, c_26])).
% 12.77/5.78  tff(c_18350, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18184, c_68, c_18347])).
% 12.77/5.78  tff(c_17041, plain, (![A_1461, B_1462]: (m1_subset_1(k2_funct_2(A_1461, B_1462), k1_zfmisc_1(k2_zfmisc_1(A_1461, A_1461))) | ~m1_subset_1(B_1462, k1_zfmisc_1(k2_zfmisc_1(A_1461, A_1461))) | ~v3_funct_2(B_1462, A_1461, A_1461) | ~v1_funct_2(B_1462, A_1461, A_1461) | ~v1_funct_1(B_1462))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_17085, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16828, c_17041])).
% 12.77/5.78  tff(c_17102, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_17085])).
% 12.77/5.78  tff(c_17841, plain, (![B_1512, C_1513, E_1511, A_1508, F_1510, D_1509]: (m1_subset_1(k1_partfun1(A_1508, B_1512, C_1513, D_1509, E_1511, F_1510), k1_zfmisc_1(k2_zfmisc_1(A_1508, D_1509))) | ~m1_subset_1(F_1510, k1_zfmisc_1(k2_zfmisc_1(C_1513, D_1509))) | ~v1_funct_1(F_1510) | ~m1_subset_1(E_1511, k1_zfmisc_1(k2_zfmisc_1(A_1508, B_1512))) | ~v1_funct_1(E_1511))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.77/5.78  tff(c_7034, plain, (![A_800, B_801, D_802]: (r2_relset_1(A_800, B_801, D_802, D_802) | ~m1_subset_1(D_802, k1_zfmisc_1(k2_zfmisc_1(A_800, B_801))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.77/5.78  tff(c_7042, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_75, c_7034])).
% 12.77/5.78  tff(c_366, plain, (![A_128, B_129, D_130]: (r2_relset_1(A_128, B_129, D_130, D_130) | ~m1_subset_1(D_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.77/5.78  tff(c_374, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_75, c_366])).
% 12.77/5.78  tff(c_550, plain, (![A_175, B_176]: (k2_funct_2(A_175, B_176)=k2_funct_1(B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(k2_zfmisc_1(A_175, A_175))) | ~v3_funct_2(B_176, A_175, A_175) | ~v1_funct_2(B_176, A_175, A_175) | ~v1_funct_1(B_176))), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.77/5.78  tff(c_560, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_550])).
% 12.77/5.78  tff(c_565, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_560])).
% 12.77/5.78  tff(c_533, plain, (![A_172, B_173]: (v1_funct_1(k2_funct_2(A_172, B_173)) | ~m1_subset_1(B_173, k1_zfmisc_1(k2_zfmisc_1(A_172, A_172))) | ~v3_funct_2(B_173, A_172, A_172) | ~v1_funct_2(B_173, A_172, A_172) | ~v1_funct_1(B_173))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_543, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_533])).
% 12.77/5.78  tff(c_548, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_543])).
% 12.77/5.78  tff(c_566, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_565, c_548])).
% 12.77/5.78  tff(c_376, plain, (r2_relset_1('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_366])).
% 12.77/5.78  tff(c_12, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.77/5.78  tff(c_117, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.77/5.78  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_117])).
% 12.77/5.78  tff(c_181, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.77/5.78  tff(c_194, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_181])).
% 12.77/5.78  tff(c_228, plain, (![B_100, A_101]: (k2_relat_1(B_100)=A_101 | ~v2_funct_2(B_100, A_101) | ~v5_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.77/5.78  tff(c_237, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_194, c_228])).
% 12.77/5.78  tff(c_246, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_237])).
% 12.77/5.78  tff(c_247, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_246])).
% 12.77/5.78  tff(c_336, plain, (![C_125, B_126, A_127]: (v2_funct_2(C_125, B_126) | ~v3_funct_2(C_125, A_127, B_126) | ~v1_funct_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.77/5.78  tff(c_346, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_336])).
% 12.77/5.78  tff(c_351, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_346])).
% 12.77/5.78  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_351])).
% 12.77/5.78  tff(c_354, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_246])).
% 12.77/5.78  tff(c_393, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.77/5.78  tff(c_403, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_393])).
% 12.77/5.78  tff(c_407, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_403])).
% 12.77/5.78  tff(c_422, plain, (![C_144, A_145, B_146]: (v2_funct_1(C_144) | ~v3_funct_2(C_144, A_145, B_146) | ~v1_funct_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.77/5.78  tff(c_432, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_422])).
% 12.77/5.78  tff(c_437, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_432])).
% 12.77/5.78  tff(c_742, plain, (![A_192, B_193]: (m1_subset_1(k2_funct_2(A_192, B_193), k1_zfmisc_1(k2_zfmisc_1(A_192, A_192))) | ~m1_subset_1(B_193, k1_zfmisc_1(k2_zfmisc_1(A_192, A_192))) | ~v3_funct_2(B_193, A_192, A_192) | ~v1_funct_2(B_193, A_192, A_192) | ~v1_funct_1(B_193))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_786, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_565, c_742])).
% 12.77/5.78  tff(c_803, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_786])).
% 12.77/5.78  tff(c_633, plain, (![A_188, B_189, C_190]: (r2_hidden('#skF_1'(A_188, B_189, C_190), A_188) | r2_relset_1(A_188, A_188, B_189, C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.77/5.78  tff(c_643, plain, (![B_189]: (r2_hidden('#skF_1'('#skF_2', B_189, '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', B_189, '#skF_3') | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))))), inference(resolution, [status(thm)], [c_68, c_633])).
% 12.77/5.78  tff(c_844, plain, (r2_hidden('#skF_1'('#skF_2', k2_funct_1('#skF_3'), '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_803, c_643])).
% 12.77/5.78  tff(c_871, plain, (r2_relset_1('#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_844])).
% 12.77/5.78  tff(c_949, plain, (k2_funct_1('#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_871, c_26])).
% 12.77/5.78  tff(c_952, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_803, c_68, c_949])).
% 12.77/5.78  tff(c_644, plain, (![B_191]: (r2_hidden('#skF_1'('#skF_2', B_191, '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', B_191, '#skF_3') | ~m1_subset_1(B_191, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))))), inference(resolution, [status(thm)], [c_68, c_633])).
% 12.77/5.78  tff(c_656, plain, (r2_hidden('#skF_1'('#skF_2', k6_partfun1('#skF_2'), '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_75, c_644])).
% 12.77/5.78  tff(c_660, plain, (r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_656])).
% 12.77/5.78  tff(c_662, plain, (k6_partfun1('#skF_2')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_660, c_26])).
% 12.77/5.78  tff(c_665, plain, (k6_partfun1('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_68, c_662])).
% 12.77/5.78  tff(c_1044, plain, (![B_210, C_211, A_212]: (k6_partfun1(B_210)=k5_relat_1(k2_funct_1(C_211), C_211) | k1_xboole_0=B_210 | ~v2_funct_1(C_211) | k2_relset_1(A_212, B_210, C_211)!=B_210 | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_212, B_210))) | ~v1_funct_2(C_211, A_212, B_210) | ~v1_funct_1(C_211))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.77/5.78  tff(c_1053, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1044])).
% 12.77/5.78  tff(c_1060, plain, (k5_relat_1('#skF_3', '#skF_3')='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_407, c_437, c_952, c_665, c_1053])).
% 12.77/5.78  tff(c_1061, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1060])).
% 12.77/5.78  tff(c_1063, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_2])).
% 12.77/5.78  tff(c_1035, plain, (![A_209]: (r2_hidden('#skF_1'('#skF_2', A_209, '#skF_3'), '#skF_2') | r2_relset_1('#skF_2', '#skF_2', A_209, '#skF_3') | ~r1_tarski(A_209, k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_12, c_644])).
% 12.77/5.78  tff(c_214, plain, (![C_91, B_92, A_93]: (~v1_xboole_0(C_91) | ~m1_subset_1(B_92, k1_zfmisc_1(C_91)) | ~r2_hidden(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.77/5.78  tff(c_222, plain, (![B_4, A_93, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_93, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_12, c_214])).
% 12.77/5.78  tff(c_1038, plain, (![B_4, A_209]: (~v1_xboole_0(B_4) | ~r1_tarski('#skF_2', B_4) | r2_relset_1('#skF_2', '#skF_2', A_209, '#skF_3') | ~r1_tarski(A_209, k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_1035, c_222])).
% 12.77/5.78  tff(c_1151, plain, (![B_227]: (~v1_xboole_0(B_227) | ~r1_tarski('#skF_2', B_227))), inference(splitLeft, [status(thm)], [c_1038])).
% 12.77/5.78  tff(c_1155, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1151])).
% 12.77/5.78  tff(c_1159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1155])).
% 12.77/5.78  tff(c_1161, plain, (![A_228]: (r2_relset_1('#skF_2', '#skF_2', A_228, '#skF_3') | ~r1_tarski(A_228, k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitRight, [status(thm)], [c_1038])).
% 12.77/5.78  tff(c_1177, plain, (r2_relset_1('#skF_2', '#skF_2', k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_8, c_1161])).
% 12.77/5.78  tff(c_1179, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_1177, c_26])).
% 12.77/5.78  tff(c_1182, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_3' | ~m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1179])).
% 12.77/5.78  tff(c_1183, plain, (~m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1182])).
% 12.77/5.78  tff(c_1186, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_1183])).
% 12.77/5.78  tff(c_1190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1186])).
% 12.77/5.78  tff(c_1191, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1182])).
% 12.77/5.78  tff(c_90, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.77/5.78  tff(c_102, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_90])).
% 12.77/5.78  tff(c_104, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.77/5.78  tff(c_112, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_102, c_104])).
% 12.77/5.78  tff(c_212, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_112])).
% 12.77/5.78  tff(c_1281, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_212])).
% 12.77/5.78  tff(c_1287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1281])).
% 12.77/5.78  tff(c_1288, plain, (k5_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_1060])).
% 12.77/5.78  tff(c_1017, plain, (![A_206, D_204, B_205, F_207, E_203, C_208]: (k1_partfun1(A_206, B_205, C_208, D_204, E_203, F_207)=k5_relat_1(E_203, F_207) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(C_208, D_204))) | ~v1_funct_1(F_207) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))) | ~v1_funct_1(E_203))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.77/5.78  tff(c_1026, plain, (![A_206, B_205, E_203]: (k1_partfun1(A_206, B_205, '#skF_2', '#skF_2', E_203, '#skF_3')=k5_relat_1(E_203, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))) | ~v1_funct_1(E_203))), inference(resolution, [status(thm)], [c_68, c_1017])).
% 12.77/5.78  tff(c_1294, plain, (![A_235, B_236, E_237]: (k1_partfun1(A_235, B_236, '#skF_2', '#skF_2', E_237, '#skF_3')=k5_relat_1(E_237, '#skF_3') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~v1_funct_1(E_237))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1026])).
% 12.77/5.78  tff(c_1307, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_3')=k5_relat_1('#skF_3', '#skF_3') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1294])).
% 12.77/5.78  tff(c_1313, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1288, c_1307])).
% 12.77/5.78  tff(c_66, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2')) | ~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 12.77/5.78  tff(c_89, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitLeft, [status(thm)], [c_66])).
% 12.77/5.78  tff(c_567, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_565, c_89])).
% 12.77/5.78  tff(c_667, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_665, c_567])).
% 12.77/5.78  tff(c_962, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_952, c_667])).
% 12.77/5.78  tff(c_1314, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1313, c_962])).
% 12.77/5.78  tff(c_1318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_1314])).
% 12.77/5.78  tff(c_1319, plain, (r2_hidden('#skF_1'('#skF_2', k2_funct_1('#skF_3'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_844])).
% 12.77/5.78  tff(c_1465, plain, (![B_253]: (~v1_xboole_0(B_253) | ~r1_tarski('#skF_2', B_253))), inference(resolution, [status(thm)], [c_1319, c_222])).
% 12.77/5.78  tff(c_1470, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1465])).
% 12.77/5.78  tff(c_1490, plain, (![B_254, C_255, A_256]: (k6_partfun1(B_254)=k5_relat_1(k2_funct_1(C_255), C_255) | k1_xboole_0=B_254 | ~v2_funct_1(C_255) | k2_relset_1(A_256, B_254, C_255)!=B_254 | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_254))) | ~v1_funct_2(C_255, A_256, B_254) | ~v1_funct_1(C_255))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.77/5.78  tff(c_1501, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1490])).
% 12.77/5.78  tff(c_1511, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_407, c_437, c_665, c_1501])).
% 12.77/5.78  tff(c_1516, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1511])).
% 12.77/5.78  tff(c_1518, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1516, c_2])).
% 12.77/5.78  tff(c_1520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1470, c_1518])).
% 12.77/5.78  tff(c_1522, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1511])).
% 12.77/5.78  tff(c_1620, plain, (![A_258, C_259, B_260]: (k6_partfun1(A_258)=k5_relat_1(C_259, k2_funct_1(C_259)) | k1_xboole_0=B_260 | ~v2_funct_1(C_259) | k2_relset_1(A_258, B_260, C_259)!=B_260 | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_258, B_260))) | ~v1_funct_2(C_259, A_258, B_260) | ~v1_funct_1(C_259))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.77/5.78  tff(c_1633, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1620])).
% 12.77/5.78  tff(c_1648, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_407, c_437, c_665, c_1633])).
% 12.77/5.78  tff(c_1649, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1522, c_1648])).
% 12.77/5.78  tff(c_1441, plain, (![C_252, B_249, A_250, D_248, F_251, E_247]: (k1_partfun1(A_250, B_249, C_252, D_248, E_247, F_251)=k5_relat_1(E_247, F_251) | ~m1_subset_1(F_251, k1_zfmisc_1(k2_zfmisc_1(C_252, D_248))) | ~v1_funct_1(F_251) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))) | ~v1_funct_1(E_247))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.77/5.78  tff(c_1443, plain, (![A_250, B_249, E_247]: (k1_partfun1(A_250, B_249, '#skF_2', '#skF_2', E_247, k2_funct_1('#skF_3'))=k5_relat_1(E_247, k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1(E_247, k1_zfmisc_1(k2_zfmisc_1(A_250, B_249))) | ~v1_funct_1(E_247))), inference(resolution, [status(thm)], [c_803, c_1441])).
% 12.77/5.78  tff(c_3673, plain, (![A_478, B_479, E_480]: (k1_partfun1(A_478, B_479, '#skF_2', '#skF_2', E_480, k2_funct_1('#skF_3'))=k5_relat_1(E_480, k2_funct_1('#skF_3')) | ~m1_subset_1(E_480, k1_zfmisc_1(k2_zfmisc_1(A_478, B_479))) | ~v1_funct_1(E_480))), inference(demodulation, [status(thm), theory('equality')], [c_566, c_1443])).
% 12.77/5.78  tff(c_3695, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3673])).
% 12.77/5.78  tff(c_3705, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1649, c_3695])).
% 12.77/5.78  tff(c_3734, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3705, c_667])).
% 12.77/5.78  tff(c_3739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_376, c_3734])).
% 12.77/5.78  tff(c_3740, plain, (r2_hidden('#skF_1'('#skF_2', k6_partfun1('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_656])).
% 12.77/5.78  tff(c_3749, plain, (![B_488]: (~v1_xboole_0(B_488) | ~r1_tarski('#skF_2', B_488))), inference(resolution, [status(thm)], [c_3740, c_222])).
% 12.77/5.78  tff(c_3754, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_3749])).
% 12.77/5.78  tff(c_4460, plain, (![A_541, C_542, B_543]: (k6_partfun1(A_541)=k5_relat_1(C_542, k2_funct_1(C_542)) | k1_xboole_0=B_543 | ~v2_funct_1(C_542) | k2_relset_1(A_541, B_543, C_542)!=B_543 | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_541, B_543))) | ~v1_funct_2(C_542, A_541, B_543) | ~v1_funct_1(C_542))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.77/5.78  tff(c_4473, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_4460])).
% 12.77/5.78  tff(c_4486, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_407, c_437, c_4473])).
% 12.77/5.78  tff(c_4493, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4486])).
% 12.77/5.78  tff(c_4495, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4493, c_2])).
% 12.77/5.78  tff(c_4497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3754, c_4495])).
% 12.77/5.78  tff(c_4498, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_4486])).
% 12.77/5.78  tff(c_3769, plain, (![A_494, B_495]: (m1_subset_1(k2_funct_2(A_494, B_495), k1_zfmisc_1(k2_zfmisc_1(A_494, A_494))) | ~m1_subset_1(B_495, k1_zfmisc_1(k2_zfmisc_1(A_494, A_494))) | ~v3_funct_2(B_495, A_494, A_494) | ~v1_funct_2(B_495, A_494, A_494) | ~v1_funct_1(B_495))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_3813, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_565, c_3769])).
% 12.77/5.78  tff(c_3830, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_3813])).
% 12.77/5.78  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.77/5.78  tff(c_3897, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_3830, c_10])).
% 12.77/5.78  tff(c_4302, plain, (![D_533, E_532, F_536, A_535, C_537, B_534]: (k1_partfun1(A_535, B_534, C_537, D_533, E_532, F_536)=k5_relat_1(E_532, F_536) | ~m1_subset_1(F_536, k1_zfmisc_1(k2_zfmisc_1(C_537, D_533))) | ~v1_funct_1(F_536) | ~m1_subset_1(E_532, k1_zfmisc_1(k2_zfmisc_1(A_535, B_534))) | ~v1_funct_1(E_532))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.77/5.78  tff(c_6572, plain, (![A_730, C_733, D_728, E_732, A_731, B_729]: (k1_partfun1(A_730, B_729, C_733, D_728, E_732, A_731)=k5_relat_1(E_732, A_731) | ~v1_funct_1(A_731) | ~m1_subset_1(E_732, k1_zfmisc_1(k2_zfmisc_1(A_730, B_729))) | ~v1_funct_1(E_732) | ~r1_tarski(A_731, k2_zfmisc_1(C_733, D_728)))), inference(resolution, [status(thm)], [c_12, c_4302])).
% 12.77/5.78  tff(c_6587, plain, (![C_733, D_728, A_731]: (k1_partfun1('#skF_2', '#skF_2', C_733, D_728, '#skF_3', A_731)=k5_relat_1('#skF_3', A_731) | ~v1_funct_1(A_731) | ~v1_funct_1('#skF_3') | ~r1_tarski(A_731, k2_zfmisc_1(C_733, D_728)))), inference(resolution, [status(thm)], [c_68, c_6572])).
% 12.77/5.78  tff(c_6598, plain, (![C_734, D_735, A_736]: (k1_partfun1('#skF_2', '#skF_2', C_734, D_735, '#skF_3', A_736)=k5_relat_1('#skF_3', A_736) | ~v1_funct_1(A_736) | ~r1_tarski(A_736, k2_zfmisc_1(C_734, D_735)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6587])).
% 12.77/5.78  tff(c_6607, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3897, c_6598])).
% 12.77/5.78  tff(c_6621, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_4498, c_6607])).
% 12.77/5.78  tff(c_6629, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6621, c_567])).
% 12.77/5.78  tff(c_6634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_374, c_6629])).
% 12.77/5.78  tff(c_6635, plain, (k2_zfmisc_1('#skF_2', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_112])).
% 12.77/5.78  tff(c_6638, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6635, c_68])).
% 12.77/5.78  tff(c_7349, plain, (![A_857, B_858]: (k2_funct_2(A_857, B_858)=k2_funct_1(B_858) | ~m1_subset_1(B_858, k1_zfmisc_1(k2_zfmisc_1(A_857, A_857))) | ~v3_funct_2(B_858, A_857, A_857) | ~v1_funct_2(B_858, A_857, A_857) | ~v1_funct_1(B_858))), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.77/5.78  tff(c_7362, plain, (![B_859]: (k2_funct_2('#skF_2', B_859)=k2_funct_1(B_859) | ~m1_subset_1(B_859, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_859, '#skF_2', '#skF_2') | ~v1_funct_2(B_859, '#skF_2', '#skF_2') | ~v1_funct_1(B_859))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_7349])).
% 12.77/5.78  tff(c_7368, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6638, c_7362])).
% 12.77/5.78  tff(c_7376, plain, (k2_funct_2('#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_7368])).
% 12.77/5.78  tff(c_7305, plain, (![A_850, B_851]: (v1_funct_1(k2_funct_2(A_850, B_851)) | ~m1_subset_1(B_851, k1_zfmisc_1(k2_zfmisc_1(A_850, A_850))) | ~v3_funct_2(B_851, A_850, A_850) | ~v1_funct_2(B_851, A_850, A_850) | ~v1_funct_1(B_851))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_7319, plain, (![B_853]: (v1_funct_1(k2_funct_2('#skF_2', B_853)) | ~m1_subset_1(B_853, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_853, '#skF_2', '#skF_2') | ~v1_funct_2(B_853, '#skF_2', '#skF_2') | ~v1_funct_1(B_853))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_7305])).
% 12.77/5.78  tff(c_7325, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6638, c_7319])).
% 12.77/5.78  tff(c_7333, plain, (v1_funct_1(k2_funct_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_7325])).
% 12.77/5.78  tff(c_7378, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7376, c_7333])).
% 12.77/5.78  tff(c_6774, plain, (![B_754, A_755]: (k2_relat_1(B_754)=A_755 | ~v2_funct_2(B_754, A_755) | ~v5_relat_1(B_754, A_755) | ~v1_relat_1(B_754))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.77/5.78  tff(c_6786, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_194, c_6774])).
% 12.77/5.78  tff(c_6796, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6786])).
% 12.77/5.78  tff(c_6797, plain, (~v2_funct_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_6796])).
% 12.77/5.78  tff(c_6964, plain, (![C_788, B_789, A_790]: (v2_funct_2(C_788, B_789) | ~v3_funct_2(C_788, A_790, B_789) | ~v1_funct_1(C_788) | ~m1_subset_1(C_788, k1_zfmisc_1(k2_zfmisc_1(A_790, B_789))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.77/5.78  tff(c_6998, plain, (![C_796]: (v2_funct_2(C_796, '#skF_2') | ~v3_funct_2(C_796, '#skF_2', '#skF_2') | ~v1_funct_1(C_796) | ~m1_subset_1(C_796, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_6964])).
% 12.77/5.78  tff(c_7004, plain, (v2_funct_2('#skF_3', '#skF_2') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6638, c_6998])).
% 12.77/5.78  tff(c_7012, plain, (v2_funct_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_7004])).
% 12.77/5.78  tff(c_7014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6797, c_7012])).
% 12.77/5.78  tff(c_7015, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_6796])).
% 12.77/5.78  tff(c_7090, plain, (![A_813, B_814, C_815]: (k2_relset_1(A_813, B_814, C_815)=k2_relat_1(C_815) | ~m1_subset_1(C_815, k1_zfmisc_1(k2_zfmisc_1(A_813, B_814))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.77/5.78  tff(c_7125, plain, (![C_820]: (k2_relset_1('#skF_2', '#skF_2', C_820)=k2_relat_1(C_820) | ~m1_subset_1(C_820, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_7090])).
% 12.77/5.78  tff(c_7131, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6638, c_7125])).
% 12.77/5.78  tff(c_7139, plain, (k2_relset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7015, c_7131])).
% 12.77/5.78  tff(c_7103, plain, (![C_816, A_817, B_818]: (v2_funct_1(C_816) | ~v3_funct_2(C_816, A_817, B_818) | ~v1_funct_1(C_816) | ~m1_subset_1(C_816, k1_zfmisc_1(k2_zfmisc_1(A_817, B_818))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.77/5.78  tff(c_7145, plain, (![C_821]: (v2_funct_1(C_821) | ~v3_funct_2(C_821, '#skF_2', '#skF_2') | ~v1_funct_1(C_821) | ~m1_subset_1(C_821, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_7103])).
% 12.77/5.78  tff(c_7151, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6638, c_7145])).
% 12.77/5.78  tff(c_7159, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_7151])).
% 12.77/5.78  tff(c_7428, plain, (![A_868, B_869]: (v3_funct_2(k2_funct_2(A_868, B_869), A_868, A_868) | ~m1_subset_1(B_869, k1_zfmisc_1(k2_zfmisc_1(A_868, A_868))) | ~v3_funct_2(B_869, A_868, A_868) | ~v1_funct_2(B_869, A_868, A_868) | ~v1_funct_1(B_869))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_7454, plain, (![B_871]: (v3_funct_2(k2_funct_2('#skF_2', B_871), '#skF_2', '#skF_2') | ~m1_subset_1(B_871, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_871, '#skF_2', '#skF_2') | ~v1_funct_2(B_871, '#skF_2', '#skF_2') | ~v1_funct_1(B_871))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_7428])).
% 12.77/5.78  tff(c_7466, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7376, c_7454])).
% 12.77/5.78  tff(c_7471, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_6638, c_7466])).
% 12.77/5.78  tff(c_7160, plain, (![A_3]: (v2_funct_1(A_3) | ~v3_funct_2(A_3, '#skF_2', '#skF_2') | ~v1_funct_1(A_3) | ~r1_tarski(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_7145])).
% 12.77/5.78  tff(c_7480, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_7471, c_7160])).
% 12.77/5.78  tff(c_7489, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7378, c_7480])).
% 12.77/5.78  tff(c_7490, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_7489])).
% 12.77/5.78  tff(c_7759, plain, (![A_903, B_904]: (m1_subset_1(k2_funct_2(A_903, B_904), k1_zfmisc_1(k2_zfmisc_1(A_903, A_903))) | ~m1_subset_1(B_904, k1_zfmisc_1(k2_zfmisc_1(A_903, A_903))) | ~v3_funct_2(B_904, A_903, A_903) | ~v1_funct_2(B_904, A_903, A_903) | ~v1_funct_1(B_904))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_7806, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7376, c_7759])).
% 12.77/5.78  tff(c_7828, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_6638, c_6635, c_6635, c_7806])).
% 12.77/5.78  tff(c_7862, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_7828, c_10])).
% 12.77/5.78  tff(c_7887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7490, c_7862])).
% 12.77/5.78  tff(c_7889, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_7489])).
% 12.77/5.78  tff(c_7389, plain, (![A_860, B_861]: (v1_funct_2(k2_funct_2(A_860, B_861), A_860, A_860) | ~m1_subset_1(B_861, k1_zfmisc_1(k2_zfmisc_1(A_860, A_860))) | ~v3_funct_2(B_861, A_860, A_860) | ~v1_funct_2(B_861, A_860, A_860) | ~v1_funct_1(B_861))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_7400, plain, (![B_862]: (v1_funct_2(k2_funct_2('#skF_2', B_862), '#skF_2', '#skF_2') | ~m1_subset_1(B_862, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_862, '#skF_2', '#skF_2') | ~v1_funct_2(B_862, '#skF_2', '#skF_2') | ~v1_funct_1(B_862))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_7389])).
% 12.77/5.78  tff(c_7403, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7376, c_7400])).
% 12.77/5.78  tff(c_7405, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_6638, c_7403])).
% 12.77/5.78  tff(c_7377, plain, (![A_3]: (k2_funct_2('#skF_2', A_3)=k2_funct_1(A_3) | ~v3_funct_2(A_3, '#skF_2', '#skF_2') | ~v1_funct_2(A_3, '#skF_2', '#skF_2') | ~v1_funct_1(A_3) | ~r1_tarski(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_7362])).
% 12.77/5.78  tff(c_7474, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_7471, c_7377])).
% 12.77/5.78  tff(c_7483, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7378, c_7405, c_7474])).
% 12.77/5.78  tff(c_7936, plain, (k2_funct_2('#skF_2', k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7889, c_7483])).
% 12.77/5.78  tff(c_7391, plain, (![B_861]: (v1_funct_2(k2_funct_2('#skF_2', B_861), '#skF_2', '#skF_2') | ~m1_subset_1(B_861, k1_zfmisc_1('#skF_3')) | ~v3_funct_2(B_861, '#skF_2', '#skF_2') | ~v1_funct_2(B_861, '#skF_2', '#skF_2') | ~v1_funct_1(B_861))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_7389])).
% 12.77/5.78  tff(c_7943, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7936, c_7391])).
% 12.77/5.78  tff(c_7952, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), '#skF_2', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7378, c_7405, c_7471, c_7943])).
% 12.77/5.78  tff(c_7956, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7952])).
% 12.77/5.78  tff(c_7963, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_12, c_7956])).
% 12.77/5.78  tff(c_7967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7889, c_7963])).
% 12.77/5.78  tff(c_7969, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7952])).
% 12.77/5.78  tff(c_8463, plain, (![D_936, C_940, A_938, E_935, F_939, B_937]: (k1_partfun1(A_938, B_937, C_940, D_936, E_935, F_939)=k5_relat_1(E_935, F_939) | ~m1_subset_1(F_939, k1_zfmisc_1(k2_zfmisc_1(C_940, D_936))) | ~v1_funct_1(F_939) | ~m1_subset_1(E_935, k1_zfmisc_1(k2_zfmisc_1(A_938, B_937))) | ~v1_funct_1(E_935))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.77/5.78  tff(c_10767, plain, (![B_1075, A_1077, E_1076, A_1078, C_1074, D_1073]: (k1_partfun1(A_1078, B_1075, C_1074, D_1073, E_1076, A_1077)=k5_relat_1(E_1076, A_1077) | ~v1_funct_1(A_1077) | ~m1_subset_1(E_1076, k1_zfmisc_1(k2_zfmisc_1(A_1078, B_1075))) | ~v1_funct_1(E_1076) | ~r1_tarski(A_1077, k2_zfmisc_1(C_1074, D_1073)))), inference(resolution, [status(thm)], [c_12, c_8463])).
% 12.77/5.78  tff(c_10790, plain, (![C_1079, D_1080, E_1081, A_1082]: (k1_partfun1('#skF_2', '#skF_2', C_1079, D_1080, E_1081, A_1082)=k5_relat_1(E_1081, A_1082) | ~v1_funct_1(A_1082) | ~m1_subset_1(E_1081, k1_zfmisc_1('#skF_3')) | ~v1_funct_1(E_1081) | ~r1_tarski(A_1082, k2_zfmisc_1(C_1079, D_1080)))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_10767])).
% 12.77/5.78  tff(c_10816, plain, (![C_1079, D_1080, A_1082]: (k1_partfun1('#skF_2', '#skF_2', C_1079, D_1080, '#skF_3', A_1082)=k5_relat_1('#skF_3', A_1082) | ~v1_funct_1(A_1082) | ~v1_funct_1('#skF_3') | ~r1_tarski(A_1082, k2_zfmisc_1(C_1079, D_1080)))), inference(resolution, [status(thm)], [c_6638, c_10790])).
% 12.77/5.78  tff(c_10884, plain, (![C_1089, D_1090, A_1091]: (k1_partfun1('#skF_2', '#skF_2', C_1089, D_1090, '#skF_3', A_1091)=k5_relat_1('#skF_3', A_1091) | ~v1_funct_1(A_1091) | ~r1_tarski(A_1091, k2_zfmisc_1(C_1089, D_1090)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10816])).
% 12.77/5.78  tff(c_10901, plain, (![A_1092]: (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', A_1092)=k5_relat_1('#skF_3', A_1092) | ~v1_funct_1(A_1092) | ~r1_tarski(A_1092, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_10884])).
% 12.77/5.78  tff(c_10931, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7889, c_10901])).
% 12.77/5.78  tff(c_10968, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7378, c_10931])).
% 12.77/5.78  tff(c_8768, plain, (![C_957, B_956, E_955, F_954, A_952, D_953]: (m1_subset_1(k1_partfun1(A_952, B_956, C_957, D_953, E_955, F_954), k1_zfmisc_1(k2_zfmisc_1(A_952, D_953))) | ~m1_subset_1(F_954, k1_zfmisc_1(k2_zfmisc_1(C_957, D_953))) | ~v1_funct_1(F_954) | ~m1_subset_1(E_955, k1_zfmisc_1(k2_zfmisc_1(A_952, B_956))) | ~v1_funct_1(E_955))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.77/5.78  tff(c_8824, plain, (![B_956, C_957, E_955, F_954]: (m1_subset_1(k1_partfun1('#skF_2', B_956, C_957, '#skF_2', E_955, F_954), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(F_954, k1_zfmisc_1(k2_zfmisc_1(C_957, '#skF_2'))) | ~v1_funct_1(F_954) | ~m1_subset_1(E_955, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_956))) | ~v1_funct_1(E_955))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_8768])).
% 12.77/5.78  tff(c_10980, plain, (m1_subset_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10968, c_8824])).
% 12.77/5.78  tff(c_10992, plain, (m1_subset_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6638, c_6635, c_7378, c_7969, c_6635, c_10980])).
% 12.77/5.78  tff(c_8569, plain, (![B_942, C_943, A_944]: (k6_partfun1(B_942)=k5_relat_1(k2_funct_1(C_943), C_943) | k1_xboole_0=B_942 | ~v2_funct_1(C_943) | k2_relset_1(A_944, B_942, C_943)!=B_942 | ~m1_subset_1(C_943, k1_zfmisc_1(k2_zfmisc_1(A_944, B_942))) | ~v1_funct_2(C_943, A_944, B_942) | ~v1_funct_1(C_943))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.77/5.78  tff(c_8573, plain, (![C_943]: (k5_relat_1(k2_funct_1(C_943), C_943)=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1(C_943) | k2_relset_1('#skF_2', '#skF_2', C_943)!='#skF_2' | ~m1_subset_1(C_943, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_943, '#skF_2', '#skF_2') | ~v1_funct_1(C_943))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_8569])).
% 12.77/5.78  tff(c_10011, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_8573])).
% 12.77/5.78  tff(c_10014, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10011, c_2])).
% 12.77/5.78  tff(c_7924, plain, (![A_905, B_906, C_907]: (r2_hidden('#skF_1'(A_905, B_906, C_907), A_905) | r2_relset_1(A_905, A_905, B_906, C_907) | ~m1_subset_1(C_907, k1_zfmisc_1(k2_zfmisc_1(A_905, A_905))) | ~m1_subset_1(B_906, k1_zfmisc_1(k2_zfmisc_1(A_905, A_905))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.77/5.78  tff(c_8930, plain, (![A_966, B_967]: (r2_hidden('#skF_1'(A_966, B_967, k6_partfun1(A_966)), A_966) | r2_relset_1(A_966, A_966, B_967, k6_partfun1(A_966)) | ~m1_subset_1(B_967, k1_zfmisc_1(k2_zfmisc_1(A_966, A_966))))), inference(resolution, [status(thm)], [c_75, c_7924])).
% 12.77/5.78  tff(c_6704, plain, (![C_740, B_741, A_742]: (~v1_xboole_0(C_740) | ~m1_subset_1(B_741, k1_zfmisc_1(C_740)) | ~r2_hidden(A_742, B_741))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.77/5.78  tff(c_6716, plain, (![B_4, A_742, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_742, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_12, c_6704])).
% 12.77/5.78  tff(c_15580, plain, (![B_1271, A_1272, B_1273]: (~v1_xboole_0(B_1271) | ~r1_tarski(A_1272, B_1271) | r2_relset_1(A_1272, A_1272, B_1273, k6_partfun1(A_1272)) | ~m1_subset_1(B_1273, k1_zfmisc_1(k2_zfmisc_1(A_1272, A_1272))))), inference(resolution, [status(thm)], [c_8930, c_6716])).
% 12.77/5.78  tff(c_15656, plain, (![B_1274, B_1275]: (~v1_xboole_0(B_1274) | r2_relset_1(B_1274, B_1274, B_1275, k6_partfun1(B_1274)) | ~m1_subset_1(B_1275, k1_zfmisc_1(k2_zfmisc_1(B_1274, B_1274))))), inference(resolution, [status(thm)], [c_8, c_15580])).
% 12.77/5.78  tff(c_15663, plain, (![B_1275]: (~v1_xboole_0('#skF_2') | r2_relset_1('#skF_2', '#skF_2', B_1275, k6_partfun1('#skF_2')) | ~m1_subset_1(B_1275, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_15656])).
% 12.77/5.78  tff(c_15692, plain, (![B_1282]: (r2_relset_1('#skF_2', '#skF_2', B_1282, k6_partfun1('#skF_2')) | ~m1_subset_1(B_1282, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10014, c_15663])).
% 12.77/5.78  tff(c_7379, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7376, c_89])).
% 12.77/5.78  tff(c_10973, plain, (~r2_relset_1('#skF_2', '#skF_2', k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10968, c_7379])).
% 12.77/5.78  tff(c_15695, plain, (~m1_subset_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_15692, c_10973])).
% 12.77/5.78  tff(c_15701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10992, c_15695])).
% 12.77/5.78  tff(c_15703, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_8573])).
% 12.77/5.78  tff(c_8633, plain, (![A_946, C_947, B_948]: (k6_partfun1(A_946)=k5_relat_1(C_947, k2_funct_1(C_947)) | k1_xboole_0=B_948 | ~v2_funct_1(C_947) | k2_relset_1(A_946, B_948, C_947)!=B_948 | ~m1_subset_1(C_947, k1_zfmisc_1(k2_zfmisc_1(A_946, B_948))) | ~v1_funct_2(C_947, A_946, B_948) | ~v1_funct_1(C_947))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.77/5.78  tff(c_8637, plain, (![C_947]: (k5_relat_1(C_947, k2_funct_1(C_947))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1(C_947) | k2_relset_1('#skF_2', '#skF_2', C_947)!='#skF_2' | ~m1_subset_1(C_947, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_947, '#skF_2', '#skF_2') | ~v1_funct_1(C_947))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_8633])).
% 12.77/5.78  tff(c_15979, plain, (![C_1309]: (k5_relat_1(C_1309, k2_funct_1(C_1309))=k6_partfun1('#skF_2') | ~v2_funct_1(C_1309) | k2_relset_1('#skF_2', '#skF_2', C_1309)!='#skF_2' | ~m1_subset_1(C_1309, k1_zfmisc_1('#skF_3')) | ~v1_funct_2(C_1309, '#skF_2', '#skF_2') | ~v1_funct_1(C_1309))), inference(negUnitSimplification, [status(thm)], [c_15703, c_8637])).
% 12.77/5.78  tff(c_15999, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6638, c_15979])).
% 12.77/5.78  tff(c_16031, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_7139, c_7159, c_15999])).
% 12.77/5.78  tff(c_16055, plain, (![B_1314, E_1315, C_1313, A_1316, A_1317, D_1312]: (k1_partfun1(A_1317, B_1314, C_1313, D_1312, E_1315, A_1316)=k5_relat_1(E_1315, A_1316) | ~v1_funct_1(A_1316) | ~m1_subset_1(E_1315, k1_zfmisc_1(k2_zfmisc_1(A_1317, B_1314))) | ~v1_funct_1(E_1315) | ~r1_tarski(A_1316, k2_zfmisc_1(C_1313, D_1312)))), inference(resolution, [status(thm)], [c_12, c_8463])).
% 12.77/5.78  tff(c_16102, plain, (![C_1321, D_1322, E_1323, A_1324]: (k1_partfun1('#skF_2', '#skF_2', C_1321, D_1322, E_1323, A_1324)=k5_relat_1(E_1323, A_1324) | ~v1_funct_1(A_1324) | ~m1_subset_1(E_1323, k1_zfmisc_1('#skF_3')) | ~v1_funct_1(E_1323) | ~r1_tarski(A_1324, k2_zfmisc_1(C_1321, D_1322)))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_16055])).
% 12.77/5.78  tff(c_16122, plain, (![C_1321, D_1322, A_1324]: (k1_partfun1('#skF_2', '#skF_2', C_1321, D_1322, '#skF_3', A_1324)=k5_relat_1('#skF_3', A_1324) | ~v1_funct_1(A_1324) | ~v1_funct_1('#skF_3') | ~r1_tarski(A_1324, k2_zfmisc_1(C_1321, D_1322)))), inference(resolution, [status(thm)], [c_6638, c_16102])).
% 12.77/5.78  tff(c_16287, plain, (![C_1326, D_1327, A_1328]: (k1_partfun1('#skF_2', '#skF_2', C_1326, D_1327, '#skF_3', A_1328)=k5_relat_1('#skF_3', A_1328) | ~v1_funct_1(A_1328) | ~r1_tarski(A_1328, k2_zfmisc_1(C_1326, D_1327)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16122])).
% 12.77/5.78  tff(c_16304, plain, (![A_1329]: (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', A_1329)=k5_relat_1('#skF_3', A_1329) | ~v1_funct_1(A_1329) | ~r1_tarski(A_1329, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6635, c_16287])).
% 12.77/5.78  tff(c_16331, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7889, c_16304])).
% 12.77/5.78  tff(c_16365, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7378, c_16031, c_16331])).
% 12.77/5.78  tff(c_16370, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16365, c_7379])).
% 12.77/5.78  tff(c_16373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7042, c_16370])).
% 12.77/5.78  tff(c_16375, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_66])).
% 12.77/5.78  tff(c_16741, plain, (![D_1423, C_1424, A_1425, B_1426]: (D_1423=C_1424 | ~r2_relset_1(A_1425, B_1426, C_1424, D_1423) | ~m1_subset_1(D_1423, k1_zfmisc_1(k2_zfmisc_1(A_1425, B_1426))) | ~m1_subset_1(C_1424, k1_zfmisc_1(k2_zfmisc_1(A_1425, B_1426))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.77/5.78  tff(c_16749, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_16375, c_16741])).
% 12.77/5.78  tff(c_16762, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3'))=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_2('#skF_2', '#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_16749])).
% 12.77/5.78  tff(c_16895, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16828, c_16828, c_16762])).
% 12.77/5.78  tff(c_16896, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_16895])).
% 12.77/5.78  tff(c_17868, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_17841, c_16896])).
% 12.77/5.78  tff(c_17920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_68, c_16829, c_17102, c_17868])).
% 12.77/5.78  tff(c_17921, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_16895])).
% 12.77/5.78  tff(c_17998, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17996, c_17921])).
% 12.77/5.78  tff(c_18361, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18350, c_17998])).
% 12.77/5.78  tff(c_16374, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_2('#skF_2', '#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(splitRight, [status(thm)], [c_66])).
% 12.77/5.78  tff(c_16831, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16828, c_16374])).
% 12.77/5.78  tff(c_17999, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17996, c_16831])).
% 12.77/5.78  tff(c_18360, plain, (~r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', '#skF_3', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18350, c_17999])).
% 12.77/5.78  tff(c_18494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16524, c_18361, c_18360])).
% 12.77/5.78  tff(c_18495, plain, (r2_hidden('#skF_1'('#skF_2', k2_funct_1('#skF_3'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_18236])).
% 12.77/5.78  tff(c_16499, plain, (![C_1362, B_1363, A_1364]: (~v1_xboole_0(C_1362) | ~m1_subset_1(B_1363, k1_zfmisc_1(C_1362)) | ~r2_hidden(A_1364, B_1363))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.77/5.78  tff(c_16507, plain, (![B_4, A_1364, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_1364, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_12, c_16499])).
% 12.77/5.78  tff(c_18643, plain, (![B_1565]: (~v1_xboole_0(B_1565) | ~r1_tarski('#skF_2', B_1565))), inference(resolution, [status(thm)], [c_18495, c_16507])).
% 12.77/5.78  tff(c_18647, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_18643])).
% 12.77/5.78  tff(c_18651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18638, c_18647])).
% 12.77/5.78  tff(c_18652, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_18630])).
% 12.77/5.78  tff(c_18503, plain, (![D_1556, C_1560, A_1558, B_1557, E_1555, F_1559]: (k1_partfun1(A_1558, B_1557, C_1560, D_1556, E_1555, F_1559)=k5_relat_1(E_1555, F_1559) | ~m1_subset_1(F_1559, k1_zfmisc_1(k2_zfmisc_1(C_1560, D_1556))) | ~v1_funct_1(F_1559) | ~m1_subset_1(E_1555, k1_zfmisc_1(k2_zfmisc_1(A_1558, B_1557))) | ~v1_funct_1(E_1555))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.77/5.78  tff(c_18514, plain, (![A_1558, B_1557, E_1555]: (k1_partfun1(A_1558, B_1557, '#skF_2', '#skF_2', E_1555, '#skF_3')=k5_relat_1(E_1555, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_1555, k1_zfmisc_1(k2_zfmisc_1(A_1558, B_1557))) | ~v1_funct_1(E_1555))), inference(resolution, [status(thm)], [c_68, c_18503])).
% 12.77/5.78  tff(c_18692, plain, (![A_1570, B_1571, E_1572]: (k1_partfun1(A_1570, B_1571, '#skF_2', '#skF_2', E_1572, '#skF_3')=k5_relat_1(E_1572, '#skF_3') | ~m1_subset_1(E_1572, k1_zfmisc_1(k2_zfmisc_1(A_1570, B_1571))) | ~v1_funct_1(E_1572))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18514])).
% 12.77/5.78  tff(c_18695, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_18184, c_18692])).
% 12.77/5.78  tff(c_18711, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16829, c_18652, c_18695])).
% 12.77/5.78  tff(c_19291, plain, (~r2_relset_1('#skF_2', '#skF_2', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18711, c_17999])).
% 12.77/5.78  tff(c_19295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16524, c_19291])).
% 12.77/5.78  tff(c_19296, plain, (r2_hidden('#skF_1'('#skF_2', k6_partfun1('#skF_2'), '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_17974])).
% 12.77/5.78  tff(c_19317, plain, (![B_1591]: (~v1_xboole_0(B_1591) | ~r1_tarski('#skF_2', B_1591))), inference(resolution, [status(thm)], [c_19296, c_16507])).
% 12.77/5.78  tff(c_19322, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_8, c_19317])).
% 12.77/5.78  tff(c_19839, plain, (![B_1624, C_1625, A_1626]: (k6_partfun1(B_1624)=k5_relat_1(k2_funct_1(C_1625), C_1625) | k1_xboole_0=B_1624 | ~v2_funct_1(C_1625) | k2_relset_1(A_1626, B_1624, C_1625)!=B_1624 | ~m1_subset_1(C_1625, k1_zfmisc_1(k2_zfmisc_1(A_1626, B_1624))) | ~v1_funct_2(C_1625, A_1626, B_1624) | ~v1_funct_1(C_1625))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.77/5.78  tff(c_19850, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_2', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_19839])).
% 12.77/5.78  tff(c_19860, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_16652, c_16694, c_19850])).
% 12.77/5.78  tff(c_19885, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_19860])).
% 12.77/5.78  tff(c_19887, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19885, c_2])).
% 12.77/5.78  tff(c_19889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19322, c_19887])).
% 12.77/5.78  tff(c_19890, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_19860])).
% 12.77/5.78  tff(c_19340, plain, (![A_1596, B_1597]: (m1_subset_1(k2_funct_2(A_1596, B_1597), k1_zfmisc_1(k2_zfmisc_1(A_1596, A_1596))) | ~m1_subset_1(B_1597, k1_zfmisc_1(k2_zfmisc_1(A_1596, A_1596))) | ~v3_funct_2(B_1597, A_1596, A_1596) | ~v1_funct_2(B_1597, A_1596, A_1596) | ~v1_funct_1(B_1597))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.77/5.78  tff(c_19389, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~v3_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16828, c_19340])).
% 12.77/5.78  tff(c_19408, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_19389])).
% 12.77/5.78  tff(c_19739, plain, (![F_1621, D_1618, E_1617, C_1622, B_1619, A_1620]: (k1_partfun1(A_1620, B_1619, C_1622, D_1618, E_1617, F_1621)=k5_relat_1(E_1617, F_1621) | ~m1_subset_1(F_1621, k1_zfmisc_1(k2_zfmisc_1(C_1622, D_1618))) | ~v1_funct_1(F_1621) | ~m1_subset_1(E_1617, k1_zfmisc_1(k2_zfmisc_1(A_1620, B_1619))) | ~v1_funct_1(E_1617))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.77/5.78  tff(c_19750, plain, (![A_1620, B_1619, E_1617]: (k1_partfun1(A_1620, B_1619, '#skF_2', '#skF_2', E_1617, '#skF_3')=k5_relat_1(E_1617, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_1617, k1_zfmisc_1(k2_zfmisc_1(A_1620, B_1619))) | ~v1_funct_1(E_1617))), inference(resolution, [status(thm)], [c_68, c_19739])).
% 12.77/5.78  tff(c_19925, plain, (![A_1630, B_1631, E_1632]: (k1_partfun1(A_1630, B_1631, '#skF_2', '#skF_2', E_1632, '#skF_3')=k5_relat_1(E_1632, '#skF_3') | ~m1_subset_1(E_1632, k1_zfmisc_1(k2_zfmisc_1(A_1630, B_1631))) | ~v1_funct_1(E_1632))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_19750])).
% 12.77/5.78  tff(c_19928, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_19408, c_19925])).
% 12.77/5.78  tff(c_19944, plain, (k1_partfun1('#skF_2', '#skF_2', '#skF_2', '#skF_2', k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16829, c_19890, c_19928])).
% 12.77/5.78  tff(c_20542, plain, (~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_19944, c_16831])).
% 12.77/5.78  tff(c_20545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16522, c_20542])).
% 12.77/5.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.77/5.78  
% 12.77/5.78  Inference rules
% 12.77/5.78  ----------------------
% 12.77/5.78  #Ref     : 5
% 12.77/5.78  #Sup     : 4361
% 12.77/5.78  #Fact    : 0
% 12.77/5.78  #Define  : 0
% 12.77/5.78  #Split   : 96
% 12.77/5.78  #Chain   : 0
% 12.77/5.78  #Close   : 0
% 12.77/5.78  
% 12.77/5.78  Ordering : KBO
% 12.77/5.78  
% 12.77/5.78  Simplification rules
% 12.77/5.78  ----------------------
% 12.77/5.78  #Subsume      : 446
% 12.77/5.78  #Demod        : 7922
% 12.77/5.78  #Tautology    : 1534
% 12.77/5.78  #SimpNegUnit  : 69
% 12.77/5.78  #BackRed      : 299
% 12.77/5.78  
% 12.77/5.78  #Partial instantiations: 0
% 12.77/5.78  #Strategies tried      : 1
% 12.77/5.78  
% 12.77/5.78  Timing (in seconds)
% 12.77/5.78  ----------------------
% 12.77/5.79  Preprocessing        : 0.38
% 12.77/5.79  Parsing              : 0.21
% 12.77/5.79  CNF conversion       : 0.02
% 12.77/5.79  Main loop            : 4.52
% 12.77/5.79  Inferencing          : 1.22
% 12.77/5.79  Reduction            : 1.99
% 12.77/5.79  Demodulation         : 1.54
% 12.77/5.79  BG Simplification    : 0.09
% 12.77/5.79  Subsumption          : 0.90
% 12.77/5.79  Abstraction          : 0.14
% 12.77/5.79  MUC search           : 0.00
% 12.77/5.79  Cooper               : 0.00
% 12.77/5.79  Total                : 5.02
% 12.77/5.79  Index Insertion      : 0.00
% 12.77/5.79  Index Deletion       : 0.00
% 12.77/5.79  Index Matching       : 0.00
% 12.77/5.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
