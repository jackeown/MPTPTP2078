%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:36 EST 2020

% Result     : Theorem 15.05s
% Output     : CNFRefutation 15.46s
% Verified   : 
% Statistics : Number of formulae       :  226 (2585 expanded)
%              Number of leaves         :   42 ( 820 expanded)
%              Depth                    :   23
%              Number of atoms          :  401 (7764 expanded)
%              Number of equality atoms :  118 (2688 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_162,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v5_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc22_relat_1)).

tff(f_142,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_78,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_40027,plain,(
    ! [C_1332,A_1333,B_1334] :
      ( v1_relat_1(C_1332)
      | ~ m1_subset_1(C_1332,k1_zfmisc_1(k2_zfmisc_1(A_1333,B_1334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_40044,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_40027])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_101,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_40811,plain,(
    ! [A_1431,B_1432,C_1433] :
      ( k1_relset_1(A_1431,B_1432,C_1433) = k1_relat_1(C_1433)
      | ~ m1_subset_1(C_1433,k1_zfmisc_1(k2_zfmisc_1(A_1431,B_1432))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40834,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_40811])).

tff(c_41592,plain,(
    ! [B_1524,A_1525,C_1526] :
      ( k1_xboole_0 = B_1524
      | k1_relset_1(A_1525,B_1524,C_1526) = A_1525
      | ~ v1_funct_2(C_1526,A_1525,B_1524)
      | ~ m1_subset_1(C_1526,k1_zfmisc_1(k2_zfmisc_1(A_1525,B_1524))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_41605,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_41592])).

tff(c_41623,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_40834,c_41605])).

tff(c_41624,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_41623])).

tff(c_34,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41644,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41624,c_34])).

tff(c_41920,plain,(
    ! [A_1541] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_1541)) = A_1541
      | ~ r1_tarski(A_1541,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40044,c_41644])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_41405,plain,(
    ! [A_1510,B_1511,C_1512,D_1513] :
      ( k2_partfun1(A_1510,B_1511,C_1512,D_1513) = k7_relat_1(C_1512,D_1513)
      | ~ m1_subset_1(C_1512,k1_zfmisc_1(k2_zfmisc_1(A_1510,B_1511)))
      | ~ v1_funct_1(C_1512) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_41414,plain,(
    ! [D_1513] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1513) = k7_relat_1('#skF_4',D_1513)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_41405])).

tff(c_41429,plain,(
    ! [D_1513] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1513) = k7_relat_1('#skF_4',D_1513) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_41414])).

tff(c_5028,plain,(
    ! [A_536,B_537,C_538,D_539] :
      ( k2_partfun1(A_536,B_537,C_538,D_539) = k7_relat_1(C_538,D_539)
      | ~ m1_subset_1(C_538,k1_zfmisc_1(k2_zfmisc_1(A_536,B_537)))
      | ~ v1_funct_1(C_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5035,plain,(
    ! [D_539] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_539) = k7_relat_1('#skF_4',D_539)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_5028])).

tff(c_5047,plain,(
    ! [D_539] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_539) = k7_relat_1('#skF_4',D_539) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5035])).

tff(c_5400,plain,(
    ! [A_561,B_562,C_563,D_564] :
      ( m1_subset_1(k2_partfun1(A_561,B_562,C_563,D_564),k1_zfmisc_1(k2_zfmisc_1(A_561,B_562)))
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562)))
      | ~ v1_funct_1(C_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5430,plain,(
    ! [D_539] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_539),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5047,c_5400])).

tff(c_5456,plain,(
    ! [D_565] : m1_subset_1(k7_relat_1('#skF_4',D_565),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_5430])).

tff(c_44,plain,(
    ! [C_28,B_27,A_26] :
      ( v5_relat_1(C_28,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5504,plain,(
    ! [D_565] : v5_relat_1(k7_relat_1('#skF_4',D_565),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5456,c_44])).

tff(c_42,plain,(
    ! [C_25,A_23,B_24] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5506,plain,(
    ! [D_565] : v1_relat_1(k7_relat_1('#skF_4',D_565)) ),
    inference(resolution,[status(thm)],[c_5456,c_42])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4882,plain,(
    ! [A_515,B_516,C_517,D_518] :
      ( v1_funct_1(k2_partfun1(A_515,B_516,C_517,D_518))
      | ~ m1_subset_1(C_517,k1_zfmisc_1(k2_zfmisc_1(A_515,B_516)))
      | ~ v1_funct_1(C_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4887,plain,(
    ! [D_518] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_518))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_4882])).

tff(c_4898,plain,(
    ! [D_518] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_518)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4887])).

tff(c_5060,plain,(
    ! [D_518] : v1_funct_1(k7_relat_1('#skF_4',D_518)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5047,c_4898])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1397,plain,(
    ! [C_205,A_206,B_207] :
      ( v1_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1414,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_1397])).

tff(c_28,plain,(
    ! [C_16,A_14,B_15] :
      ( k7_relat_1(k7_relat_1(C_16,A_14),B_15) = k7_relat_1(C_16,A_14)
      | ~ r1_tarski(A_14,B_15)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2205,plain,(
    ! [C_314,A_315,B_316] :
      ( k7_relat_1(k7_relat_1(C_314,A_315),B_316) = k7_relat_1(C_314,A_315)
      | ~ r1_tarski(A_315,B_316)
      | ~ v1_relat_1(C_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_15738,plain,(
    ! [C_999,A_1000,B_1002,B_1001] :
      ( k7_relat_1(k7_relat_1(C_999,A_1000),B_1002) = k7_relat_1(k7_relat_1(C_999,A_1000),B_1001)
      | ~ r1_tarski(B_1002,B_1001)
      | ~ v1_relat_1(k7_relat_1(C_999,A_1000))
      | ~ r1_tarski(A_1000,B_1002)
      | ~ v1_relat_1(C_999) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2205])).

tff(c_15880,plain,(
    ! [C_1008,A_1009] :
      ( k7_relat_1(k7_relat_1(C_1008,A_1009),'#skF_3') = k7_relat_1(k7_relat_1(C_1008,A_1009),'#skF_1')
      | ~ v1_relat_1(k7_relat_1(C_1008,A_1009))
      | ~ r1_tarski(A_1009,'#skF_3')
      | ~ v1_relat_1(C_1008) ) ),
    inference(resolution,[status(thm)],[c_78,c_15738])).

tff(c_15910,plain,(
    ! [D_565] :
      ( k7_relat_1(k7_relat_1('#skF_4',D_565),'#skF_3') = k7_relat_1(k7_relat_1('#skF_4',D_565),'#skF_1')
      | ~ r1_tarski(D_565,'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5506,c_15880])).

tff(c_15953,plain,(
    ! [D_1010] :
      ( k7_relat_1(k7_relat_1('#skF_4',D_1010),'#skF_3') = k7_relat_1(k7_relat_1('#skF_4',D_1010),'#skF_1')
      | ~ r1_tarski(D_1010,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_15910])).

tff(c_2079,plain,(
    ! [A_296,B_297,C_298] :
      ( k1_relset_1(A_296,B_297,C_298) = k1_relat_1(C_298)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2098,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_2079])).

tff(c_5083,plain,(
    ! [B_545,A_546,C_547] :
      ( k1_xboole_0 = B_545
      | k1_relset_1(A_546,B_545,C_547) = A_546
      | ~ v1_funct_2(C_547,A_546,B_545)
      | ~ m1_subset_1(C_547,k1_zfmisc_1(k2_zfmisc_1(A_546,B_545))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5093,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_5083])).

tff(c_5108,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2098,c_5093])).

tff(c_5109,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_5108])).

tff(c_5126,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5109,c_34])).

tff(c_5195,plain,(
    ! [A_551] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_551)) = A_551
      | ~ r1_tarski(A_551,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_5126])).

tff(c_36,plain,(
    ! [A_19] :
      ( k7_relat_1(A_19,k1_relat_1(A_19)) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5221,plain,(
    ! [A_551] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_551),A_551) = k7_relat_1('#skF_4',A_551)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_551))
      | ~ r1_tarski(A_551,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5195,c_36])).

tff(c_6146,plain,(
    ! [A_551] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_551),A_551) = k7_relat_1('#skF_4',A_551)
      | ~ r1_tarski(A_551,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5506,c_5221])).

tff(c_16061,plain,
    ( k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_1') = k7_relat_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15953,c_6146])).

tff(c_16129,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_1') = k7_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_78,c_16061])).

tff(c_1512,plain,(
    ! [B_220,A_221] :
      ( v5_relat_1(B_220,A_221)
      | ~ r1_tarski(k2_relat_1(B_220),A_221)
      | ~ v1_relat_1(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1522,plain,(
    ! [B_220] :
      ( v5_relat_1(B_220,k2_relat_1(B_220))
      | ~ v1_relat_1(B_220) ) ),
    inference(resolution,[status(thm)],[c_6,c_1512])).

tff(c_1610,plain,(
    ! [C_233,A_234,B_235] :
      ( v1_relat_1(k7_relat_1(C_233,A_234))
      | ~ v5_relat_1(C_233,B_235)
      | ~ v1_relat_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1615,plain,(
    ! [B_220,A_234] :
      ( v1_relat_1(k7_relat_1(B_220,A_234))
      | ~ v1_relat_1(B_220) ) ),
    inference(resolution,[status(thm)],[c_1522,c_1610])).

tff(c_15952,plain,(
    ! [B_220,A_234] :
      ( k7_relat_1(k7_relat_1(B_220,A_234),'#skF_3') = k7_relat_1(k7_relat_1(B_220,A_234),'#skF_1')
      | ~ r1_tarski(A_234,'#skF_3')
      | ~ v1_relat_1(B_220) ) ),
    inference(resolution,[status(thm)],[c_1615,c_15880])).

tff(c_5451,plain,(
    ! [D_539] : m1_subset_1(k7_relat_1('#skF_4',D_539),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_5430])).

tff(c_66,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k2_partfun1(A_39,B_40,C_41,D_42) = k7_relat_1(C_41,D_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5464,plain,(
    ! [D_565,D_42] :
      ( k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_565),D_42) = k7_relat_1(k7_relat_1('#skF_4',D_565),D_42)
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_565)) ) ),
    inference(resolution,[status(thm)],[c_5456,c_66])).

tff(c_6454,plain,(
    ! [D_630,D_631] : k2_partfun1('#skF_1','#skF_2',k7_relat_1('#skF_4',D_630),D_631) = k7_relat_1(k7_relat_1('#skF_4',D_630),D_631) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5060,c_5464])).

tff(c_62,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( m1_subset_1(k2_partfun1(A_35,B_36,C_37,D_38),k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ v1_funct_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6460,plain,(
    ! [D_630,D_631] :
      ( m1_subset_1(k7_relat_1(k7_relat_1('#skF_4',D_630),D_631),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1(k7_relat_1('#skF_4',D_630),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1(k7_relat_1('#skF_4',D_630)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6454,c_62])).

tff(c_6506,plain,(
    ! [D_634,D_635] : m1_subset_1(k7_relat_1(k7_relat_1('#skF_4',D_634),D_635),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5060,c_5451,c_6460])).

tff(c_6568,plain,(
    ! [D_634,D_635] : v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_634),D_635)) ),
    inference(resolution,[status(thm)],[c_6506,c_42])).

tff(c_15784,plain,(
    ! [C_999,A_1000] :
      ( k7_relat_1(k7_relat_1(C_999,A_1000),'#skF_3') = k7_relat_1(k7_relat_1(C_999,A_1000),'#skF_1')
      | ~ v1_relat_1(k7_relat_1(C_999,A_1000))
      | ~ r1_tarski(A_1000,'#skF_3')
      | ~ v1_relat_1(C_999) ) ),
    inference(resolution,[status(thm)],[c_78,c_15738])).

tff(c_15959,plain,(
    ! [D_1010] :
      ( k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_1010),'#skF_3'),'#skF_3') = k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_1010),'#skF_3'),'#skF_1')
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_1010),'#skF_1'))
      | ~ r1_tarski('#skF_3','#skF_3')
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_1010))
      | ~ r1_tarski(D_1010,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15953,c_15784])).

tff(c_25889,plain,(
    ! [D_1174] :
      ( k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_1174),'#skF_3'),'#skF_3') = k7_relat_1(k7_relat_1(k7_relat_1('#skF_4',D_1174),'#skF_3'),'#skF_1')
      | ~ r1_tarski(D_1174,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5506,c_6,c_6568,c_15959])).

tff(c_25953,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3'),'#skF_1') = k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6146,c_25889])).

tff(c_26003,plain,(
    k7_relat_1(k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3'),'#skF_1') = k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6,c_25953])).

tff(c_26538,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_1'),'#skF_1') = k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15952,c_26003])).

tff(c_26583,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3') = k7_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_6,c_16129,c_16129,c_26538])).

tff(c_5218,plain,(
    ! [A_551,A_17] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_4',A_551),A_17)) = A_17
      | ~ r1_tarski(A_17,A_551)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_551))
      | ~ r1_tarski(A_551,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5195,c_34])).

tff(c_9480,plain,(
    ! [A_551,A_17] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_4',A_551),A_17)) = A_17
      | ~ r1_tarski(A_17,A_551)
      | ~ r1_tarski(A_551,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5506,c_5218])).

tff(c_26936,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26583,c_9480])).

tff(c_27053,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6,c_26936])).

tff(c_4972,plain,(
    ! [B_531,A_532] :
      ( m1_subset_1(B_531,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_531),A_532)))
      | ~ r1_tarski(k2_relat_1(B_531),A_532)
      | ~ v1_funct_1(B_531)
      | ~ v1_relat_1(B_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5011,plain,(
    ! [B_531,A_532] :
      ( r1_tarski(B_531,k2_zfmisc_1(k1_relat_1(B_531),A_532))
      | ~ r1_tarski(k2_relat_1(B_531),A_532)
      | ~ v1_funct_1(B_531)
      | ~ v1_relat_1(B_531) ) ),
    inference(resolution,[status(thm)],[c_4972,c_18])).

tff(c_27169,plain,(
    ! [A_532] :
      ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3',A_532))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),A_532)
      | ~ v1_funct_1(k7_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27053,c_5011])).

tff(c_39480,plain,(
    ! [A_1327] :
      ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3',A_1327))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),A_1327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5506,c_5060,c_27169])).

tff(c_39491,plain,(
    ! [A_12] :
      ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3',A_12))
      | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),A_12)
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_26,c_39480])).

tff(c_39970,plain,(
    ! [A_1331] :
      ( r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3',A_1331))
      | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),A_1331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5506,c_39491])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1373,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( v1_funct_1(k2_partfun1(A_201,B_202,C_203,D_204))
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202)))
      | ~ v1_funct_1(C_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1378,plain,(
    ! [D_204] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_204))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_80,c_1373])).

tff(c_1389,plain,(
    ! [D_204] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_204)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1378])).

tff(c_74,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_227,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_1393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_227])).

tff(c_1394,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1396,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1394])).

tff(c_1569,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_1396])).

tff(c_5061,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5047,c_1569])).

tff(c_39989,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_39970,c_5061])).

tff(c_40024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5504,c_39989])).

tff(c_40026,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1394])).

tff(c_40832,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40026,c_40811])).

tff(c_41434,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41429,c_41429,c_40832])).

tff(c_40025,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1394])).

tff(c_41443,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41429,c_40025])).

tff(c_41442,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41429,c_40026])).

tff(c_56,plain,(
    ! [B_33,C_34,A_32] :
      ( k1_xboole_0 = B_33
      | v1_funct_2(C_34,A_32,B_33)
      | k1_relset_1(A_32,B_33,C_34) != A_32
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_41543,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_41442,c_56])).

tff(c_41567,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_41443,c_101,c_41543])).

tff(c_41584,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41434,c_41567])).

tff(c_41926,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_41920,c_41584])).

tff(c_41975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_41926])).

tff(c_41976,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41980,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41976,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42003,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41976,c_41976,c_14])).

tff(c_41977,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_41985,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41976,c_41977])).

tff(c_42002,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41985,c_80])).

tff(c_42004,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42003,c_42002])).

tff(c_42031,plain,(
    ! [A_1549,B_1550] :
      ( r1_tarski(A_1549,B_1550)
      | ~ m1_subset_1(A_1549,k1_zfmisc_1(B_1550)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42042,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_42004,c_42031])).

tff(c_43335,plain,(
    ! [B_1699,A_1700] :
      ( B_1699 = A_1700
      | ~ r1_tarski(B_1699,A_1700)
      | ~ r1_tarski(A_1700,B_1699) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43337,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_42042,c_43335])).

tff(c_43346,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41980,c_43337])).

tff(c_41999,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41985,c_82])).

tff(c_43373,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43346,c_43346,c_41999])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42012,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41976,c_41976,c_12])).

tff(c_42123,plain,(
    ! [C_1559,A_1560,B_1561] :
      ( v1_relat_1(C_1559)
      | ~ m1_subset_1(C_1559,k1_zfmisc_1(k2_zfmisc_1(A_1560,B_1561))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_43297,plain,(
    ! [C_1697] :
      ( v1_relat_1(C_1697)
      | ~ m1_subset_1(C_1697,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42012,c_42123])).

tff(c_43310,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42004,c_43297])).

tff(c_43374,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43346,c_41980])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_41979,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41976,c_41976,c_32])).

tff(c_42045,plain,(
    ! [A_1551] :
      ( k7_relat_1(A_1551,k1_relat_1(A_1551)) = A_1551
      | ~ v1_relat_1(A_1551) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42054,plain,
    ( k7_relat_1('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_41979,c_42045])).

tff(c_42057,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42054])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_42000,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41976,c_16])).

tff(c_42099,plain,(
    ! [C_1556,A_1557,B_1558] :
      ( v1_relat_1(C_1556)
      | ~ m1_subset_1(C_1556,k1_zfmisc_1(k2_zfmisc_1(A_1557,B_1558))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42111,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_42000,c_42099])).

tff(c_42116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42057,c_42111])).

tff(c_42117,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42054])).

tff(c_43365,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43346,c_43346,c_43346,c_42117])).

tff(c_44083,plain,(
    ! [C_1795,A_1796,B_1797] :
      ( k7_relat_1(k7_relat_1(C_1795,A_1796),B_1797) = k7_relat_1(C_1795,A_1796)
      | ~ r1_tarski(A_1796,B_1797)
      | ~ v1_relat_1(C_1795) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44116,plain,(
    ! [B_1797] :
      ( k7_relat_1('#skF_4',B_1797) = k7_relat_1('#skF_4','#skF_4')
      | ~ r1_tarski('#skF_4',B_1797)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43365,c_44083])).

tff(c_44129,plain,(
    ! [B_1797] : k7_relat_1('#skF_4',B_1797) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43310,c_43374,c_43365,c_44116])).

tff(c_43372,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43346,c_42000])).

tff(c_44649,plain,(
    ! [A_1860,B_1861,C_1862,D_1863] :
      ( k2_partfun1(A_1860,B_1861,C_1862,D_1863) = k7_relat_1(C_1862,D_1863)
      | ~ m1_subset_1(C_1862,k1_zfmisc_1(k2_zfmisc_1(A_1860,B_1861)))
      | ~ v1_funct_1(C_1862) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44656,plain,(
    ! [A_1860,B_1861,D_1863] :
      ( k2_partfun1(A_1860,B_1861,'#skF_4',D_1863) = k7_relat_1('#skF_4',D_1863)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_43372,c_44649])).

tff(c_44665,plain,(
    ! [A_1860,B_1861,D_1863] : k2_partfun1(A_1860,B_1861,'#skF_4',D_1863) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_44129,c_44656])).

tff(c_43343,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_43335])).

tff(c_43354,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41980,c_43343])).

tff(c_43362,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43346,c_43354])).

tff(c_42179,plain,(
    ! [B_1564,A_1565] :
      ( B_1564 = A_1565
      | ~ r1_tarski(B_1564,A_1565)
      | ~ r1_tarski(A_1565,B_1564) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42181,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_42042,c_42179])).

tff(c_42190,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41980,c_42181])).

tff(c_42218,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42190,c_42000])).

tff(c_43277,plain,(
    ! [A_1693,B_1694,C_1695,D_1696] :
      ( v1_funct_1(k2_partfun1(A_1693,B_1694,C_1695,D_1696))
      | ~ m1_subset_1(C_1695,k1_zfmisc_1(k2_zfmisc_1(A_1693,B_1694)))
      | ~ v1_funct_1(C_1695) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_43284,plain,(
    ! [A_1693,B_1694,D_1696] :
      ( v1_funct_1(k2_partfun1(A_1693,B_1694,'#skF_4',D_1696))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42218,c_43277])).

tff(c_43290,plain,(
    ! [A_1693,B_1694,D_1696] : v1_funct_1(k2_partfun1(A_1693,B_1694,'#skF_4',D_1696)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_43284])).

tff(c_42187,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_42179])).

tff(c_42198,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41980,c_42187])).

tff(c_42139,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41985,c_41985,c_41985,c_42012,c_41985,c_41985,c_74])).

tff(c_42140,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_42139])).

tff(c_42200,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42198,c_42140])).

tff(c_42279,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42190,c_42190,c_42190,c_42200])).

tff(c_43294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43290,c_42279])).

tff(c_43295,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_42139])).

tff(c_43523,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43362,c_43346,c_43346,c_43346,c_43362,c_43362,c_43346,c_43346,c_43346,c_43295])).

tff(c_43524,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_43523])).

tff(c_43577,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_43524])).

tff(c_44668,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44665,c_43577])).

tff(c_44673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_44668])).

tff(c_44675,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_43523])).

tff(c_44725,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_44675,c_18])).

tff(c_43347,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_41980,c_43335])).

tff(c_43471,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43346,c_43346,c_43347])).

tff(c_44802,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44725,c_43471])).

tff(c_44674,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_43523])).

tff(c_44819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43373,c_44802,c_44674])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:54:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.05/6.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.46/6.92  
% 15.46/6.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.46/6.92  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.46/6.92  
% 15.46/6.92  %Foreground sorts:
% 15.46/6.92  
% 15.46/6.92  
% 15.46/6.92  %Background operators:
% 15.46/6.92  
% 15.46/6.92  
% 15.46/6.92  %Foreground operators:
% 15.46/6.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.46/6.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.46/6.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.46/6.92  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.46/6.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.46/6.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.46/6.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.46/6.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.46/6.92  tff('#skF_2', type, '#skF_2': $i).
% 15.46/6.92  tff('#skF_3', type, '#skF_3': $i).
% 15.46/6.92  tff('#skF_1', type, '#skF_1': $i).
% 15.46/6.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.46/6.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.46/6.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.46/6.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.46/6.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.46/6.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.46/6.92  tff('#skF_4', type, '#skF_4': $i).
% 15.46/6.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.46/6.92  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.46/6.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.46/6.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.46/6.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.46/6.92  
% 15.46/6.95  tff(f_162, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 15.46/6.95  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.46/6.95  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.46/6.95  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 15.46/6.95  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 15.46/6.95  tff(f_130, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 15.46/6.95  tff(f_124, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 15.46/6.95  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.46/6.95  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 15.46/6.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.46/6.95  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 15.46/6.95  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 15.46/6.95  tff(f_84, axiom, (![A, B, C]: ((v1_relat_1(C) & v5_relat_1(C, B)) => (v1_relat_1(k7_relat_1(C, A)) & v5_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc22_relat_1)).
% 15.46/6.95  tff(f_142, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 15.46/6.95  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.46/6.95  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 15.46/6.95  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.46/6.95  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 15.46/6.95  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 15.46/6.95  tff(c_78, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 15.46/6.96  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 15.46/6.96  tff(c_40027, plain, (![C_1332, A_1333, B_1334]: (v1_relat_1(C_1332) | ~m1_subset_1(C_1332, k1_zfmisc_1(k2_zfmisc_1(A_1333, B_1334))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/6.96  tff(c_40044, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_40027])).
% 15.46/6.96  tff(c_76, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_162])).
% 15.46/6.96  tff(c_101, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_76])).
% 15.46/6.96  tff(c_82, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 15.46/6.96  tff(c_40811, plain, (![A_1431, B_1432, C_1433]: (k1_relset_1(A_1431, B_1432, C_1433)=k1_relat_1(C_1433) | ~m1_subset_1(C_1433, k1_zfmisc_1(k2_zfmisc_1(A_1431, B_1432))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.46/6.96  tff(c_40834, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_40811])).
% 15.46/6.96  tff(c_41592, plain, (![B_1524, A_1525, C_1526]: (k1_xboole_0=B_1524 | k1_relset_1(A_1525, B_1524, C_1526)=A_1525 | ~v1_funct_2(C_1526, A_1525, B_1524) | ~m1_subset_1(C_1526, k1_zfmisc_1(k2_zfmisc_1(A_1525, B_1524))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.46/6.96  tff(c_41605, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_41592])).
% 15.46/6.96  tff(c_41623, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_40834, c_41605])).
% 15.46/6.96  tff(c_41624, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_101, c_41623])).
% 15.46/6.96  tff(c_34, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 15.46/6.96  tff(c_41644, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_41624, c_34])).
% 15.46/6.96  tff(c_41920, plain, (![A_1541]: (k1_relat_1(k7_relat_1('#skF_4', A_1541))=A_1541 | ~r1_tarski(A_1541, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40044, c_41644])).
% 15.46/6.96  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 15.46/6.96  tff(c_41405, plain, (![A_1510, B_1511, C_1512, D_1513]: (k2_partfun1(A_1510, B_1511, C_1512, D_1513)=k7_relat_1(C_1512, D_1513) | ~m1_subset_1(C_1512, k1_zfmisc_1(k2_zfmisc_1(A_1510, B_1511))) | ~v1_funct_1(C_1512))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.46/6.96  tff(c_41414, plain, (![D_1513]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1513)=k7_relat_1('#skF_4', D_1513) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_41405])).
% 15.46/6.96  tff(c_41429, plain, (![D_1513]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1513)=k7_relat_1('#skF_4', D_1513))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_41414])).
% 15.46/6.96  tff(c_5028, plain, (![A_536, B_537, C_538, D_539]: (k2_partfun1(A_536, B_537, C_538, D_539)=k7_relat_1(C_538, D_539) | ~m1_subset_1(C_538, k1_zfmisc_1(k2_zfmisc_1(A_536, B_537))) | ~v1_funct_1(C_538))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.46/6.96  tff(c_5035, plain, (![D_539]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_539)=k7_relat_1('#skF_4', D_539) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_5028])).
% 15.46/6.96  tff(c_5047, plain, (![D_539]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_539)=k7_relat_1('#skF_4', D_539))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5035])).
% 15.46/6.96  tff(c_5400, plain, (![A_561, B_562, C_563, D_564]: (m1_subset_1(k2_partfun1(A_561, B_562, C_563, D_564), k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))) | ~v1_funct_1(C_563))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.46/6.96  tff(c_5430, plain, (![D_539]: (m1_subset_1(k7_relat_1('#skF_4', D_539), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5047, c_5400])).
% 15.46/6.96  tff(c_5456, plain, (![D_565]: (m1_subset_1(k7_relat_1('#skF_4', D_565), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_5430])).
% 15.46/6.96  tff(c_44, plain, (![C_28, B_27, A_26]: (v5_relat_1(C_28, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.46/6.96  tff(c_5504, plain, (![D_565]: (v5_relat_1(k7_relat_1('#skF_4', D_565), '#skF_2'))), inference(resolution, [status(thm)], [c_5456, c_44])).
% 15.46/6.96  tff(c_42, plain, (![C_25, A_23, B_24]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/6.96  tff(c_5506, plain, (![D_565]: (v1_relat_1(k7_relat_1('#skF_4', D_565)))), inference(resolution, [status(thm)], [c_5456, c_42])).
% 15.46/6.96  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.46/6.96  tff(c_4882, plain, (![A_515, B_516, C_517, D_518]: (v1_funct_1(k2_partfun1(A_515, B_516, C_517, D_518)) | ~m1_subset_1(C_517, k1_zfmisc_1(k2_zfmisc_1(A_515, B_516))) | ~v1_funct_1(C_517))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.46/6.96  tff(c_4887, plain, (![D_518]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_518)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_4882])).
% 15.46/6.96  tff(c_4898, plain, (![D_518]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_518)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4887])).
% 15.46/6.96  tff(c_5060, plain, (![D_518]: (v1_funct_1(k7_relat_1('#skF_4', D_518)))), inference(demodulation, [status(thm), theory('equality')], [c_5047, c_4898])).
% 15.46/6.96  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.46/6.96  tff(c_1397, plain, (![C_205, A_206, B_207]: (v1_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/6.96  tff(c_1414, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_1397])).
% 15.46/6.96  tff(c_28, plain, (![C_16, A_14, B_15]: (k7_relat_1(k7_relat_1(C_16, A_14), B_15)=k7_relat_1(C_16, A_14) | ~r1_tarski(A_14, B_15) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.46/6.96  tff(c_2205, plain, (![C_314, A_315, B_316]: (k7_relat_1(k7_relat_1(C_314, A_315), B_316)=k7_relat_1(C_314, A_315) | ~r1_tarski(A_315, B_316) | ~v1_relat_1(C_314))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.46/6.96  tff(c_15738, plain, (![C_999, A_1000, B_1002, B_1001]: (k7_relat_1(k7_relat_1(C_999, A_1000), B_1002)=k7_relat_1(k7_relat_1(C_999, A_1000), B_1001) | ~r1_tarski(B_1002, B_1001) | ~v1_relat_1(k7_relat_1(C_999, A_1000)) | ~r1_tarski(A_1000, B_1002) | ~v1_relat_1(C_999))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2205])).
% 15.46/6.96  tff(c_15880, plain, (![C_1008, A_1009]: (k7_relat_1(k7_relat_1(C_1008, A_1009), '#skF_3')=k7_relat_1(k7_relat_1(C_1008, A_1009), '#skF_1') | ~v1_relat_1(k7_relat_1(C_1008, A_1009)) | ~r1_tarski(A_1009, '#skF_3') | ~v1_relat_1(C_1008))), inference(resolution, [status(thm)], [c_78, c_15738])).
% 15.46/6.96  tff(c_15910, plain, (![D_565]: (k7_relat_1(k7_relat_1('#skF_4', D_565), '#skF_3')=k7_relat_1(k7_relat_1('#skF_4', D_565), '#skF_1') | ~r1_tarski(D_565, '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5506, c_15880])).
% 15.46/6.96  tff(c_15953, plain, (![D_1010]: (k7_relat_1(k7_relat_1('#skF_4', D_1010), '#skF_3')=k7_relat_1(k7_relat_1('#skF_4', D_1010), '#skF_1') | ~r1_tarski(D_1010, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_15910])).
% 15.46/6.96  tff(c_2079, plain, (![A_296, B_297, C_298]: (k1_relset_1(A_296, B_297, C_298)=k1_relat_1(C_298) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.46/6.96  tff(c_2098, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_2079])).
% 15.46/6.96  tff(c_5083, plain, (![B_545, A_546, C_547]: (k1_xboole_0=B_545 | k1_relset_1(A_546, B_545, C_547)=A_546 | ~v1_funct_2(C_547, A_546, B_545) | ~m1_subset_1(C_547, k1_zfmisc_1(k2_zfmisc_1(A_546, B_545))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.46/6.96  tff(c_5093, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_5083])).
% 15.46/6.96  tff(c_5108, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2098, c_5093])).
% 15.46/6.96  tff(c_5109, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_101, c_5108])).
% 15.46/6.96  tff(c_5126, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5109, c_34])).
% 15.46/6.96  tff(c_5195, plain, (![A_551]: (k1_relat_1(k7_relat_1('#skF_4', A_551))=A_551 | ~r1_tarski(A_551, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_5126])).
% 15.46/6.96  tff(c_36, plain, (![A_19]: (k7_relat_1(A_19, k1_relat_1(A_19))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.46/6.96  tff(c_5221, plain, (![A_551]: (k7_relat_1(k7_relat_1('#skF_4', A_551), A_551)=k7_relat_1('#skF_4', A_551) | ~v1_relat_1(k7_relat_1('#skF_4', A_551)) | ~r1_tarski(A_551, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5195, c_36])).
% 15.46/6.96  tff(c_6146, plain, (![A_551]: (k7_relat_1(k7_relat_1('#skF_4', A_551), A_551)=k7_relat_1('#skF_4', A_551) | ~r1_tarski(A_551, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5506, c_5221])).
% 15.46/6.96  tff(c_16061, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_1')=k7_relat_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15953, c_6146])).
% 15.46/6.96  tff(c_16129, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_1')=k7_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_78, c_16061])).
% 15.46/6.96  tff(c_1512, plain, (![B_220, A_221]: (v5_relat_1(B_220, A_221) | ~r1_tarski(k2_relat_1(B_220), A_221) | ~v1_relat_1(B_220))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.46/6.96  tff(c_1522, plain, (![B_220]: (v5_relat_1(B_220, k2_relat_1(B_220)) | ~v1_relat_1(B_220))), inference(resolution, [status(thm)], [c_6, c_1512])).
% 15.46/6.96  tff(c_1610, plain, (![C_233, A_234, B_235]: (v1_relat_1(k7_relat_1(C_233, A_234)) | ~v5_relat_1(C_233, B_235) | ~v1_relat_1(C_233))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.46/6.96  tff(c_1615, plain, (![B_220, A_234]: (v1_relat_1(k7_relat_1(B_220, A_234)) | ~v1_relat_1(B_220))), inference(resolution, [status(thm)], [c_1522, c_1610])).
% 15.46/6.96  tff(c_15952, plain, (![B_220, A_234]: (k7_relat_1(k7_relat_1(B_220, A_234), '#skF_3')=k7_relat_1(k7_relat_1(B_220, A_234), '#skF_1') | ~r1_tarski(A_234, '#skF_3') | ~v1_relat_1(B_220))), inference(resolution, [status(thm)], [c_1615, c_15880])).
% 15.46/6.96  tff(c_5451, plain, (![D_539]: (m1_subset_1(k7_relat_1('#skF_4', D_539), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_5430])).
% 15.46/6.96  tff(c_66, plain, (![A_39, B_40, C_41, D_42]: (k2_partfun1(A_39, B_40, C_41, D_42)=k7_relat_1(C_41, D_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_1(C_41))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.46/6.96  tff(c_5464, plain, (![D_565, D_42]: (k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_565), D_42)=k7_relat_1(k7_relat_1('#skF_4', D_565), D_42) | ~v1_funct_1(k7_relat_1('#skF_4', D_565)))), inference(resolution, [status(thm)], [c_5456, c_66])).
% 15.46/6.96  tff(c_6454, plain, (![D_630, D_631]: (k2_partfun1('#skF_1', '#skF_2', k7_relat_1('#skF_4', D_630), D_631)=k7_relat_1(k7_relat_1('#skF_4', D_630), D_631))), inference(demodulation, [status(thm), theory('equality')], [c_5060, c_5464])).
% 15.46/6.96  tff(c_62, plain, (![A_35, B_36, C_37, D_38]: (m1_subset_1(k2_partfun1(A_35, B_36, C_37, D_38), k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~v1_funct_1(C_37))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.46/6.96  tff(c_6460, plain, (![D_630, D_631]: (m1_subset_1(k7_relat_1(k7_relat_1('#skF_4', D_630), D_631), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1(k7_relat_1('#skF_4', D_630), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1(k7_relat_1('#skF_4', D_630)))), inference(superposition, [status(thm), theory('equality')], [c_6454, c_62])).
% 15.46/6.96  tff(c_6506, plain, (![D_634, D_635]: (m1_subset_1(k7_relat_1(k7_relat_1('#skF_4', D_634), D_635), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_5060, c_5451, c_6460])).
% 15.46/6.96  tff(c_6568, plain, (![D_634, D_635]: (v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_634), D_635)))), inference(resolution, [status(thm)], [c_6506, c_42])).
% 15.46/6.96  tff(c_15784, plain, (![C_999, A_1000]: (k7_relat_1(k7_relat_1(C_999, A_1000), '#skF_3')=k7_relat_1(k7_relat_1(C_999, A_1000), '#skF_1') | ~v1_relat_1(k7_relat_1(C_999, A_1000)) | ~r1_tarski(A_1000, '#skF_3') | ~v1_relat_1(C_999))), inference(resolution, [status(thm)], [c_78, c_15738])).
% 15.46/6.96  tff(c_15959, plain, (![D_1010]: (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_1010), '#skF_3'), '#skF_3')=k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_1010), '#skF_3'), '#skF_1') | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_1010), '#skF_1')) | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', D_1010)) | ~r1_tarski(D_1010, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_15953, c_15784])).
% 15.46/6.96  tff(c_25889, plain, (![D_1174]: (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_1174), '#skF_3'), '#skF_3')=k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', D_1174), '#skF_3'), '#skF_1') | ~r1_tarski(D_1174, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5506, c_6, c_6568, c_15959])).
% 15.46/6.96  tff(c_25953, plain, (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3'), '#skF_1')=k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6146, c_25889])).
% 15.46/6.96  tff(c_26003, plain, (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3'), '#skF_1')=k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6, c_25953])).
% 15.46/6.96  tff(c_26538, plain, (k7_relat_1(k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_1'), '#skF_1')=k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15952, c_26003])).
% 15.46/6.96  tff(c_26583, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3')=k7_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_6, c_16129, c_16129, c_26538])).
% 15.46/6.96  tff(c_5218, plain, (![A_551, A_17]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_4', A_551), A_17))=A_17 | ~r1_tarski(A_17, A_551) | ~v1_relat_1(k7_relat_1('#skF_4', A_551)) | ~r1_tarski(A_551, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5195, c_34])).
% 15.46/6.96  tff(c_9480, plain, (![A_551, A_17]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_4', A_551), A_17))=A_17 | ~r1_tarski(A_17, A_551) | ~r1_tarski(A_551, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5506, c_5218])).
% 15.46/6.96  tff(c_26936, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26583, c_9480])).
% 15.46/6.96  tff(c_27053, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6, c_26936])).
% 15.46/6.96  tff(c_4972, plain, (![B_531, A_532]: (m1_subset_1(B_531, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_531), A_532))) | ~r1_tarski(k2_relat_1(B_531), A_532) | ~v1_funct_1(B_531) | ~v1_relat_1(B_531))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.46/6.96  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.46/6.96  tff(c_5011, plain, (![B_531, A_532]: (r1_tarski(B_531, k2_zfmisc_1(k1_relat_1(B_531), A_532)) | ~r1_tarski(k2_relat_1(B_531), A_532) | ~v1_funct_1(B_531) | ~v1_relat_1(B_531))), inference(resolution, [status(thm)], [c_4972, c_18])).
% 15.46/6.96  tff(c_27169, plain, (![A_532]: (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', A_532)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), A_532) | ~v1_funct_1(k7_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_27053, c_5011])).
% 15.46/6.96  tff(c_39480, plain, (![A_1327]: (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', A_1327)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), A_1327))), inference(demodulation, [status(thm), theory('equality')], [c_5506, c_5060, c_27169])).
% 15.46/6.96  tff(c_39491, plain, (![A_12]: (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', A_12)) | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), A_12) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_26, c_39480])).
% 15.46/6.96  tff(c_39970, plain, (![A_1331]: (r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', A_1331)) | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), A_1331))), inference(demodulation, [status(thm), theory('equality')], [c_5506, c_39491])).
% 15.46/6.96  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.46/6.96  tff(c_1373, plain, (![A_201, B_202, C_203, D_204]: (v1_funct_1(k2_partfun1(A_201, B_202, C_203, D_204)) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))) | ~v1_funct_1(C_203))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.46/6.96  tff(c_1378, plain, (![D_204]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_204)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_1373])).
% 15.46/6.96  tff(c_1389, plain, (![D_204]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_204)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1378])).
% 15.46/6.96  tff(c_74, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 15.46/6.96  tff(c_227, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 15.46/6.96  tff(c_1393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1389, c_227])).
% 15.46/6.96  tff(c_1394, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_74])).
% 15.46/6.96  tff(c_1396, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1394])).
% 15.46/6.96  tff(c_1569, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_1396])).
% 15.46/6.96  tff(c_5061, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5047, c_1569])).
% 15.46/6.96  tff(c_39989, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_39970, c_5061])).
% 15.46/6.96  tff(c_40024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5504, c_39989])).
% 15.46/6.96  tff(c_40026, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1394])).
% 15.46/6.96  tff(c_40832, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_40026, c_40811])).
% 15.46/6.96  tff(c_41434, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_41429, c_41429, c_40832])).
% 15.46/6.96  tff(c_40025, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1394])).
% 15.46/6.96  tff(c_41443, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_41429, c_40025])).
% 15.46/6.96  tff(c_41442, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_41429, c_40026])).
% 15.46/6.96  tff(c_56, plain, (![B_33, C_34, A_32]: (k1_xboole_0=B_33 | v1_funct_2(C_34, A_32, B_33) | k1_relset_1(A_32, B_33, C_34)!=A_32 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 15.46/6.96  tff(c_41543, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_41442, c_56])).
% 15.46/6.96  tff(c_41567, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_41443, c_101, c_41543])).
% 15.46/6.96  tff(c_41584, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_41434, c_41567])).
% 15.46/6.96  tff(c_41926, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_41920, c_41584])).
% 15.46/6.96  tff(c_41975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_41926])).
% 15.46/6.96  tff(c_41976, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_76])).
% 15.46/6.96  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 15.46/6.96  tff(c_41980, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_41976, c_8])).
% 15.46/6.96  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.46/6.96  tff(c_42003, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41976, c_41976, c_14])).
% 15.46/6.96  tff(c_41977, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_76])).
% 15.46/6.96  tff(c_41985, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41976, c_41977])).
% 15.46/6.96  tff(c_42002, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41985, c_80])).
% 15.46/6.96  tff(c_42004, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42003, c_42002])).
% 15.46/6.96  tff(c_42031, plain, (![A_1549, B_1550]: (r1_tarski(A_1549, B_1550) | ~m1_subset_1(A_1549, k1_zfmisc_1(B_1550)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.46/6.96  tff(c_42042, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_42004, c_42031])).
% 15.46/6.96  tff(c_43335, plain, (![B_1699, A_1700]: (B_1699=A_1700 | ~r1_tarski(B_1699, A_1700) | ~r1_tarski(A_1700, B_1699))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.46/6.96  tff(c_43337, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_42042, c_43335])).
% 15.46/6.96  tff(c_43346, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41980, c_43337])).
% 15.46/6.96  tff(c_41999, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41985, c_82])).
% 15.46/6.96  tff(c_43373, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43346, c_43346, c_41999])).
% 15.46/6.96  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.46/6.96  tff(c_42012, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41976, c_41976, c_12])).
% 15.46/6.96  tff(c_42123, plain, (![C_1559, A_1560, B_1561]: (v1_relat_1(C_1559) | ~m1_subset_1(C_1559, k1_zfmisc_1(k2_zfmisc_1(A_1560, B_1561))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/6.96  tff(c_43297, plain, (![C_1697]: (v1_relat_1(C_1697) | ~m1_subset_1(C_1697, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_42012, c_42123])).
% 15.46/6.96  tff(c_43310, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42004, c_43297])).
% 15.46/6.96  tff(c_43374, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_43346, c_41980])).
% 15.46/6.96  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 15.46/6.96  tff(c_41979, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41976, c_41976, c_32])).
% 15.46/6.96  tff(c_42045, plain, (![A_1551]: (k7_relat_1(A_1551, k1_relat_1(A_1551))=A_1551 | ~v1_relat_1(A_1551))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.46/6.96  tff(c_42054, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_41979, c_42045])).
% 15.46/6.96  tff(c_42057, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_42054])).
% 15.46/6.96  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.46/6.96  tff(c_42000, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_41976, c_16])).
% 15.46/6.96  tff(c_42099, plain, (![C_1556, A_1557, B_1558]: (v1_relat_1(C_1556) | ~m1_subset_1(C_1556, k1_zfmisc_1(k2_zfmisc_1(A_1557, B_1558))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/6.96  tff(c_42111, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_42000, c_42099])).
% 15.46/6.96  tff(c_42116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42057, c_42111])).
% 15.46/6.96  tff(c_42117, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_42054])).
% 15.46/6.96  tff(c_43365, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43346, c_43346, c_43346, c_42117])).
% 15.46/6.96  tff(c_44083, plain, (![C_1795, A_1796, B_1797]: (k7_relat_1(k7_relat_1(C_1795, A_1796), B_1797)=k7_relat_1(C_1795, A_1796) | ~r1_tarski(A_1796, B_1797) | ~v1_relat_1(C_1795))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.46/6.96  tff(c_44116, plain, (![B_1797]: (k7_relat_1('#skF_4', B_1797)=k7_relat_1('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', B_1797) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_43365, c_44083])).
% 15.46/6.96  tff(c_44129, plain, (![B_1797]: (k7_relat_1('#skF_4', B_1797)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43310, c_43374, c_43365, c_44116])).
% 15.46/6.96  tff(c_43372, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_43346, c_42000])).
% 15.46/6.96  tff(c_44649, plain, (![A_1860, B_1861, C_1862, D_1863]: (k2_partfun1(A_1860, B_1861, C_1862, D_1863)=k7_relat_1(C_1862, D_1863) | ~m1_subset_1(C_1862, k1_zfmisc_1(k2_zfmisc_1(A_1860, B_1861))) | ~v1_funct_1(C_1862))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.46/6.96  tff(c_44656, plain, (![A_1860, B_1861, D_1863]: (k2_partfun1(A_1860, B_1861, '#skF_4', D_1863)=k7_relat_1('#skF_4', D_1863) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_43372, c_44649])).
% 15.46/6.96  tff(c_44665, plain, (![A_1860, B_1861, D_1863]: (k2_partfun1(A_1860, B_1861, '#skF_4', D_1863)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_44129, c_44656])).
% 15.46/6.96  tff(c_43343, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_43335])).
% 15.46/6.96  tff(c_43354, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41980, c_43343])).
% 15.46/6.96  tff(c_43362, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_43346, c_43354])).
% 15.46/6.96  tff(c_42179, plain, (![B_1564, A_1565]: (B_1564=A_1565 | ~r1_tarski(B_1564, A_1565) | ~r1_tarski(A_1565, B_1564))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.46/6.96  tff(c_42181, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_42042, c_42179])).
% 15.46/6.96  tff(c_42190, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41980, c_42181])).
% 15.46/6.96  tff(c_42218, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_42190, c_42000])).
% 15.46/6.96  tff(c_43277, plain, (![A_1693, B_1694, C_1695, D_1696]: (v1_funct_1(k2_partfun1(A_1693, B_1694, C_1695, D_1696)) | ~m1_subset_1(C_1695, k1_zfmisc_1(k2_zfmisc_1(A_1693, B_1694))) | ~v1_funct_1(C_1695))), inference(cnfTransformation, [status(thm)], [f_124])).
% 15.46/6.96  tff(c_43284, plain, (![A_1693, B_1694, D_1696]: (v1_funct_1(k2_partfun1(A_1693, B_1694, '#skF_4', D_1696)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_42218, c_43277])).
% 15.46/6.96  tff(c_43290, plain, (![A_1693, B_1694, D_1696]: (v1_funct_1(k2_partfun1(A_1693, B_1694, '#skF_4', D_1696)))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_43284])).
% 15.46/6.96  tff(c_42187, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_42179])).
% 15.46/6.96  tff(c_42198, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41980, c_42187])).
% 15.46/6.96  tff(c_42139, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_41985, c_41985, c_41985, c_42012, c_41985, c_41985, c_74])).
% 15.46/6.96  tff(c_42140, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_42139])).
% 15.46/6.96  tff(c_42200, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42198, c_42140])).
% 15.46/6.96  tff(c_42279, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42190, c_42190, c_42190, c_42200])).
% 15.46/6.96  tff(c_43294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43290, c_42279])).
% 15.46/6.96  tff(c_43295, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_42139])).
% 15.46/6.96  tff(c_43523, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_43362, c_43346, c_43346, c_43346, c_43362, c_43362, c_43346, c_43346, c_43346, c_43295])).
% 15.46/6.96  tff(c_43524, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_43523])).
% 15.46/6.96  tff(c_43577, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_43524])).
% 15.46/6.96  tff(c_44668, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44665, c_43577])).
% 15.46/6.96  tff(c_44673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_44668])).
% 15.46/6.96  tff(c_44675, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_43523])).
% 15.46/6.96  tff(c_44725, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_44675, c_18])).
% 15.46/6.96  tff(c_43347, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_41980, c_43335])).
% 15.46/6.96  tff(c_43471, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_43346, c_43346, c_43347])).
% 15.46/6.96  tff(c_44802, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_44725, c_43471])).
% 15.46/6.96  tff(c_44674, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_43523])).
% 15.46/6.96  tff(c_44819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43373, c_44802, c_44674])).
% 15.46/6.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.46/6.96  
% 15.46/6.96  Inference rules
% 15.46/6.96  ----------------------
% 15.46/6.96  #Ref     : 0
% 15.46/6.96  #Sup     : 9328
% 15.46/6.96  #Fact    : 0
% 15.46/6.96  #Define  : 0
% 15.46/6.96  #Split   : 40
% 15.46/6.96  #Chain   : 0
% 15.46/6.96  #Close   : 0
% 15.46/6.96  
% 15.46/6.96  Ordering : KBO
% 15.46/6.96  
% 15.46/6.96  Simplification rules
% 15.46/6.96  ----------------------
% 15.46/6.96  #Subsume      : 2876
% 15.46/6.96  #Demod        : 15607
% 15.46/6.96  #Tautology    : 3482
% 15.46/6.96  #SimpNegUnit  : 241
% 15.46/6.96  #BackRed      : 125
% 15.46/6.96  
% 15.46/6.96  #Partial instantiations: 0
% 15.46/6.96  #Strategies tried      : 1
% 15.46/6.96  
% 15.46/6.96  Timing (in seconds)
% 15.46/6.96  ----------------------
% 15.46/6.96  Preprocessing        : 0.38
% 15.46/6.96  Parsing              : 0.20
% 15.46/6.96  CNF conversion       : 0.03
% 15.46/6.96  Main loop            : 5.69
% 15.46/6.96  Inferencing          : 1.43
% 15.46/6.96  Reduction            : 2.42
% 15.46/6.96  Demodulation         : 1.89
% 15.46/6.96  BG Simplification    : 0.12
% 15.46/6.96  Subsumption          : 1.39
% 15.46/6.96  Abstraction          : 0.20
% 15.46/6.96  MUC search           : 0.00
% 15.46/6.96  Cooper               : 0.00
% 15.46/6.96  Total                : 6.14
% 15.46/6.96  Index Insertion      : 0.00
% 15.46/6.96  Index Deletion       : 0.00
% 15.46/6.96  Index Matching       : 0.00
% 15.46/6.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
