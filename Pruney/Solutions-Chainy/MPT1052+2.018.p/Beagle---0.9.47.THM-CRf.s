%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:11 EST 2020

% Result     : Theorem 10.00s
% Output     : CNFRefutation 10.31s
% Verified   : 
% Statistics : Number of formulae       :  178 (1260 expanded)
%              Number of leaves         :   40 ( 417 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 (2739 expanded)
%              Number of equality atoms :  132 ( 703 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_108,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_64,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_148,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_176,plain,(
    ! [A_58,B_59] :
      ( v1_xboole_0(k1_funct_2(A_58,B_59))
      | ~ v1_xboole_0(B_59)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_66,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_2])).

tff(c_183,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_176,c_91])).

tff(c_185,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_425,plain,(
    ! [C_485,A_486,B_487] :
      ( v1_funct_2(C_485,A_486,B_487)
      | ~ r2_hidden(C_485,k1_funct_2(A_486,B_487)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_443,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_425])).

tff(c_589,plain,(
    ! [C_502,A_503,B_504] :
      ( m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_503,B_504)))
      | ~ r2_hidden(C_502,k1_funct_2(A_503,B_504)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_635,plain,(
    ! [C_511,A_512,B_513] :
      ( r1_tarski(C_511,k2_zfmisc_1(A_512,B_513))
      | ~ r2_hidden(C_511,k1_funct_2(A_512,B_513)) ) ),
    inference(resolution,[status(thm)],[c_589,c_14])).

tff(c_656,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_635])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_657,plain,(
    ! [A_514,B_515,C_516] :
      ( k1_relset_1(A_514,B_515,C_516) = k1_relat_1(C_516)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1414,plain,(
    ! [A_544,B_545,A_546] :
      ( k1_relset_1(A_544,B_545,A_546) = k1_relat_1(A_546)
      | ~ r1_tarski(A_546,k2_zfmisc_1(A_544,B_545)) ) ),
    inference(resolution,[status(thm)],[c_16,c_657])).

tff(c_1440,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_656,c_1414])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( k2_relat_1(k2_zfmisc_1(A_16,B_17)) = B_17
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1492,plain,(
    ! [A_551,B_552] :
      ( r1_tarski(k2_relat_1(A_551),k2_relat_1(B_552))
      | ~ r1_tarski(A_551,B_552)
      | ~ v1_relat_1(B_552)
      | ~ v1_relat_1(A_551) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1498,plain,(
    ! [A_551,B_17,A_16] :
      ( r1_tarski(k2_relat_1(A_551),B_17)
      | ~ r1_tarski(A_551,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_551)
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1492])).

tff(c_4556,plain,(
    ! [A_1626,B_1627,A_1628] :
      ( r1_tarski(k2_relat_1(A_1626),B_1627)
      | ~ r1_tarski(A_1626,k2_zfmisc_1(A_1628,B_1627))
      | ~ v1_relat_1(A_1626)
      | k1_xboole_0 = B_1627
      | k1_xboole_0 = A_1628 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1498])).

tff(c_4566,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_656,c_4556])).

tff(c_4589,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4566])).

tff(c_4599,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4589])).

tff(c_56,plain,(
    ! [C_32,A_30,B_31] :
      ( m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ r2_hidden(C_32,k1_funct_2(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3046,plain,(
    ! [B_1579,A_1580,C_1581] :
      ( k1_xboole_0 = B_1579
      | k1_relset_1(A_1580,B_1579,C_1581) = A_1580
      | ~ v1_funct_2(C_1581,A_1580,B_1579)
      | ~ m1_subset_1(C_1581,k1_zfmisc_1(k2_zfmisc_1(A_1580,B_1579))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3060,plain,(
    ! [B_31,A_30,C_32] :
      ( k1_xboole_0 = B_31
      | k1_relset_1(A_30,B_31,C_32) = A_30
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ r2_hidden(C_32,k1_funct_2(A_30,B_31)) ) ),
    inference(resolution,[status(thm)],[c_56,c_3046])).

tff(c_4901,plain,(
    ! [B_1636,A_1637,C_1638] :
      ( B_1636 = '#skF_2'
      | k1_relset_1(A_1637,B_1636,C_1638) = A_1637
      | ~ v1_funct_2(C_1638,A_1637,B_1636)
      | ~ r2_hidden(C_1638,k1_funct_2(A_1637,B_1636)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4599,c_3060])).

tff(c_4911,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_4901])).

tff(c_4916,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_1440,c_4911])).

tff(c_4917,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_4916])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4704,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4599,c_6])).

tff(c_4933,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4917,c_4704])).

tff(c_4942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_4933])).

tff(c_4944,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4589])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( k1_relat_1(k2_zfmisc_1(A_16,B_17)) = A_16
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_952,plain,(
    ! [A_527,B_528] :
      ( r1_tarski(k1_relat_1(A_527),k1_relat_1(B_528))
      | ~ r1_tarski(A_527,B_528)
      | ~ v1_relat_1(B_528)
      | ~ v1_relat_1(A_527) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_958,plain,(
    ! [A_527,A_16,B_17] :
      ( r1_tarski(k1_relat_1(A_527),A_16)
      | ~ r1_tarski(A_527,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_527)
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_952])).

tff(c_5321,plain,(
    ! [A_1648,A_1649,B_1650] :
      ( r1_tarski(k1_relat_1(A_1648),A_1649)
      | ~ r1_tarski(A_1648,k2_zfmisc_1(A_1649,B_1650))
      | ~ v1_relat_1(A_1648)
      | k1_xboole_0 = B_1650
      | k1_xboole_0 = A_1649 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_958])).

tff(c_5331,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_656,c_5321])).

tff(c_5354,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5331])).

tff(c_5355,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4944,c_5354])).

tff(c_5365,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5355])).

tff(c_5475,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5365,c_6])).

tff(c_5477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_5475])).

tff(c_5479,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5355])).

tff(c_6993,plain,(
    ! [B_1661,A_1662,C_1663] :
      ( k1_xboole_0 = B_1661
      | k1_relset_1(A_1662,B_1661,C_1663) = A_1662
      | ~ v1_funct_2(C_1663,A_1662,B_1661)
      | ~ r2_hidden(C_1663,k1_funct_2(A_1662,B_1661)) ) ),
    inference(resolution,[status(thm)],[c_56,c_3046])).

tff(c_7072,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_6993])).

tff(c_7089,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_1440,c_7072])).

tff(c_7091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_5479,c_7089])).

tff(c_7093,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_7101,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7093,c_8])).

tff(c_7092,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_7097,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7092,c_8])).

tff(c_7119,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7101,c_7097])).

tff(c_7128,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7119,c_66])).

tff(c_121,plain,(
    ! [A_46,B_47] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_46,B_47)),B_47) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_126,plain,(
    ! [A_46] : k2_relat_1(k2_zfmisc_1(A_46,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_121,c_12])).

tff(c_7106,plain,(
    ! [A_46] : k2_relat_1(k2_zfmisc_1(A_46,'#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7097,c_7097,c_126])).

tff(c_7188,plain,(
    ! [A_46] : k2_relat_1(k2_zfmisc_1(A_46,'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7119,c_7119,c_7106])).

tff(c_160,plain,(
    ! [A_53] :
      ( k2_relat_1(A_53) != k1_xboole_0
      | k1_xboole_0 = A_53
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_167,plain,(
    ! [A_10,B_11] :
      ( k2_relat_1(k2_zfmisc_1(A_10,B_11)) != k1_xboole_0
      | k2_zfmisc_1(A_10,B_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_7480,plain,(
    ! [A_1695,B_1696] :
      ( k2_relat_1(k2_zfmisc_1(A_1695,B_1696)) != '#skF_3'
      | k2_zfmisc_1(A_1695,B_1696) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7101,c_7101,c_167])).

tff(c_7495,plain,(
    ! [A_1697] : k2_zfmisc_1(A_1697,'#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7188,c_7480])).

tff(c_7634,plain,(
    ! [C_1700,A_1701] :
      ( m1_subset_1(C_1700,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_1700,k1_funct_2(A_1701,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7495,c_56])).

tff(c_7650,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7128,c_7634])).

tff(c_7655,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_7650,c_14])).

tff(c_7108,plain,(
    ! [A_7] :
      ( A_7 = '#skF_2'
      | ~ r1_tarski(A_7,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7097,c_7097,c_12])).

tff(c_7221,plain,(
    ! [A_7] :
      ( A_7 = '#skF_3'
      | ~ r1_tarski(A_7,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7119,c_7119,c_7108])).

tff(c_7659,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7655,c_7221])).

tff(c_7126,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7119,c_148])).

tff(c_7686,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7659,c_7126])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7112,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7097,c_7097,c_34])).

tff(c_7134,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7119,c_7119,c_7112])).

tff(c_7690,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7659,c_7659,c_7134])).

tff(c_7727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7686,c_7690])).

tff(c_7729,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_138,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) != k1_xboole_0
      | k1_xboole_0 = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_146,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_138])).

tff(c_147,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_7734,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7729,c_147])).

tff(c_7762,plain,(
    ! [A_1713,B_1714] :
      ( v1_xboole_0(k1_funct_2(A_1713,B_1714))
      | ~ v1_xboole_0(B_1714)
      | v1_xboole_0(A_1713) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7769,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_7762,c_91])).

tff(c_7795,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_7769])).

tff(c_7728,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8364,plain,(
    ! [C_2140,A_2141,B_2142] :
      ( m1_subset_1(C_2140,k1_zfmisc_1(k2_zfmisc_1(A_2141,B_2142)))
      | ~ r2_hidden(C_2140,k1_funct_2(A_2141,B_2142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8498,plain,(
    ! [C_2150,A_2151,B_2152] :
      ( r1_tarski(C_2150,k2_zfmisc_1(A_2151,B_2152))
      | ~ r2_hidden(C_2150,k1_funct_2(A_2151,B_2152)) ) ),
    inference(resolution,[status(thm)],[c_8364,c_14])).

tff(c_8536,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_66,c_8498])).

tff(c_8831,plain,(
    ! [A_2178,B_2179] :
      ( r1_tarski(k2_relat_1(A_2178),k2_relat_1(B_2179))
      | ~ r1_tarski(A_2178,B_2179)
      | ~ v1_relat_1(B_2179)
      | ~ v1_relat_1(A_2178) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8837,plain,(
    ! [A_2178,B_17,A_16] :
      ( r1_tarski(k2_relat_1(A_2178),B_17)
      | ~ r1_tarski(A_2178,k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(k2_zfmisc_1(A_16,B_17))
      | ~ v1_relat_1(A_2178)
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8831])).

tff(c_10587,plain,(
    ! [A_2262,B_2263,A_2264] :
      ( r1_tarski(k2_relat_1(A_2262),B_2263)
      | ~ r1_tarski(A_2262,k2_zfmisc_1(A_2264,B_2263))
      | ~ v1_relat_1(A_2262)
      | k1_xboole_0 = B_2263
      | k1_xboole_0 = A_2264 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8837])).

tff(c_10595,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8536,c_10587])).

tff(c_10618,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10595])).

tff(c_10619,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_7734,c_7728,c_10618])).

tff(c_10718,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10619,c_6])).

tff(c_10720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7795,c_10718])).

tff(c_10721,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7769])).

tff(c_10725,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10721,c_8])).

tff(c_10729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7734,c_10725])).

tff(c_10730,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10737,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10730,c_10])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10738,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10730,c_10730,c_32])).

tff(c_10739,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10730,c_10730,c_34])).

tff(c_10745,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_10746,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10739,c_10745])).

tff(c_10740,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10730,c_6])).

tff(c_11001,plain,(
    ! [C_2291,A_2292,B_2293] :
      ( v1_funct_2(C_2291,A_2292,B_2293)
      | ~ r2_hidden(C_2291,k1_funct_2(A_2292,B_2293)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_11019,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_11001])).

tff(c_12274,plain,(
    ! [A_2343,B_2344,C_2345] :
      ( k1_relset_1(A_2343,B_2344,C_2345) = k1_relat_1(C_2345)
      | ~ m1_subset_1(C_2345,k1_zfmisc_1(k2_zfmisc_1(A_2343,B_2344))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12636,plain,(
    ! [A_2370,B_2371,A_2372] :
      ( k1_relset_1(A_2370,B_2371,A_2372) = k1_relat_1(A_2372)
      | ~ r1_tarski(A_2372,k2_zfmisc_1(A_2370,B_2371)) ) ),
    inference(resolution,[status(thm)],[c_16,c_12274])).

tff(c_12653,plain,(
    ! [A_2370,B_2371] : k1_relset_1(A_2370,B_2371,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10737,c_12636])).

tff(c_12665,plain,(
    ! [A_2370,B_2371] : k1_relset_1(A_2370,B_2371,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10739,c_12653])).

tff(c_52,plain,(
    ! [B_26,A_25,C_27] :
      ( k1_xboole_0 = B_26
      | k1_relset_1(A_25,B_26,C_27) = A_25
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_13808,plain,(
    ! [B_3299,A_3300,C_3301] :
      ( B_3299 = '#skF_4'
      | k1_relset_1(A_3300,B_3299,C_3301) = A_3300
      | ~ v1_funct_2(C_3301,A_3300,B_3299)
      | ~ m1_subset_1(C_3301,k1_zfmisc_1(k2_zfmisc_1(A_3300,B_3299))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10730,c_52])).

tff(c_19770,plain,(
    ! [B_3377,A_3378,C_3379] :
      ( B_3377 = '#skF_4'
      | k1_relset_1(A_3378,B_3377,C_3379) = A_3378
      | ~ v1_funct_2(C_3379,A_3378,B_3377)
      | ~ r2_hidden(C_3379,k1_funct_2(A_3378,B_3377)) ) ),
    inference(resolution,[status(thm)],[c_56,c_13808])).

tff(c_19873,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_19770])).

tff(c_19892,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11019,c_12665,c_19873])).

tff(c_19893,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_10746,c_19892])).

tff(c_10846,plain,(
    ! [A_2279,B_2280] :
      ( v1_xboole_0(k1_funct_2(A_2279,B_2280))
      | ~ v1_xboole_0(B_2280)
      | v1_xboole_0(A_2279) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10854,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_10846,c_91])).

tff(c_10855,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_10854])).

tff(c_19917,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19893,c_10855])).

tff(c_19924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10740,c_19917])).

tff(c_19925,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_10854])).

tff(c_10736,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10730,c_8])).

tff(c_19929,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19925,c_10736])).

tff(c_19933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10746,c_19929])).

tff(c_19934,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_19958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10737,c_10738,c_19934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.00/3.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.16/3.62  
% 10.16/3.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.16/3.63  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 10.16/3.63  
% 10.16/3.63  %Foreground sorts:
% 10.16/3.63  
% 10.16/3.63  
% 10.16/3.63  %Background operators:
% 10.16/3.63  
% 10.16/3.63  
% 10.16/3.63  %Foreground operators:
% 10.16/3.63  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 10.16/3.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.16/3.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.16/3.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.16/3.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.16/3.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.16/3.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.16/3.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.16/3.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.16/3.63  tff('#skF_2', type, '#skF_2': $i).
% 10.16/3.63  tff('#skF_3', type, '#skF_3': $i).
% 10.16/3.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.16/3.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.16/3.63  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 10.16/3.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.16/3.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.16/3.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.16/3.63  tff('#skF_4', type, '#skF_4': $i).
% 10.16/3.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.16/3.63  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 10.16/3.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.16/3.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.16/3.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.16/3.63  
% 10.31/3.65  tff(f_136, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 10.31/3.65  tff(f_115, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 10.31/3.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.31/3.65  tff(f_123, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 10.31/3.65  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.31/3.65  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.31/3.65  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.31/3.65  tff(f_64, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 10.31/3.65  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 10.31/3.65  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.31/3.65  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.31/3.65  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.31/3.65  tff(f_52, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 10.31/3.65  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 10.31/3.65  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 10.31/3.65  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 10.31/3.65  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.31/3.65  tff(c_64, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.31/3.65  tff(c_148, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 10.31/3.65  tff(c_176, plain, (![A_58, B_59]: (v1_xboole_0(k1_funct_2(A_58, B_59)) | ~v1_xboole_0(B_59) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.31/3.65  tff(c_66, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.31/3.65  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.31/3.65  tff(c_91, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_2])).
% 10.31/3.65  tff(c_183, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_176, c_91])).
% 10.31/3.65  tff(c_185, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_183])).
% 10.31/3.65  tff(c_425, plain, (![C_485, A_486, B_487]: (v1_funct_2(C_485, A_486, B_487) | ~r2_hidden(C_485, k1_funct_2(A_486, B_487)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.31/3.65  tff(c_443, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_425])).
% 10.31/3.65  tff(c_589, plain, (![C_502, A_503, B_504]: (m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_503, B_504))) | ~r2_hidden(C_502, k1_funct_2(A_503, B_504)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.31/3.65  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.31/3.65  tff(c_635, plain, (![C_511, A_512, B_513]: (r1_tarski(C_511, k2_zfmisc_1(A_512, B_513)) | ~r2_hidden(C_511, k1_funct_2(A_512, B_513)))), inference(resolution, [status(thm)], [c_589, c_14])).
% 10.31/3.65  tff(c_656, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_635])).
% 10.31/3.65  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.31/3.65  tff(c_657, plain, (![A_514, B_515, C_516]: (k1_relset_1(A_514, B_515, C_516)=k1_relat_1(C_516) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_515))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.31/3.65  tff(c_1414, plain, (![A_544, B_545, A_546]: (k1_relset_1(A_544, B_545, A_546)=k1_relat_1(A_546) | ~r1_tarski(A_546, k2_zfmisc_1(A_544, B_545)))), inference(resolution, [status(thm)], [c_16, c_657])).
% 10.31/3.65  tff(c_1440, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_656, c_1414])).
% 10.31/3.65  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.31/3.65  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.31/3.65  tff(c_24, plain, (![A_16, B_17]: (k2_relat_1(k2_zfmisc_1(A_16, B_17))=B_17 | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.31/3.65  tff(c_1492, plain, (![A_551, B_552]: (r1_tarski(k2_relat_1(A_551), k2_relat_1(B_552)) | ~r1_tarski(A_551, B_552) | ~v1_relat_1(B_552) | ~v1_relat_1(A_551))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.31/3.65  tff(c_1498, plain, (![A_551, B_17, A_16]: (r1_tarski(k2_relat_1(A_551), B_17) | ~r1_tarski(A_551, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_551) | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_24, c_1492])).
% 10.31/3.65  tff(c_4556, plain, (![A_1626, B_1627, A_1628]: (r1_tarski(k2_relat_1(A_1626), B_1627) | ~r1_tarski(A_1626, k2_zfmisc_1(A_1628, B_1627)) | ~v1_relat_1(A_1626) | k1_xboole_0=B_1627 | k1_xboole_0=A_1628)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1498])).
% 10.31/3.65  tff(c_4566, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_656, c_4556])).
% 10.31/3.65  tff(c_4589, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4566])).
% 10.31/3.65  tff(c_4599, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4589])).
% 10.31/3.65  tff(c_56, plain, (![C_32, A_30, B_31]: (m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~r2_hidden(C_32, k1_funct_2(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.31/3.65  tff(c_3046, plain, (![B_1579, A_1580, C_1581]: (k1_xboole_0=B_1579 | k1_relset_1(A_1580, B_1579, C_1581)=A_1580 | ~v1_funct_2(C_1581, A_1580, B_1579) | ~m1_subset_1(C_1581, k1_zfmisc_1(k2_zfmisc_1(A_1580, B_1579))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.31/3.65  tff(c_3060, plain, (![B_31, A_30, C_32]: (k1_xboole_0=B_31 | k1_relset_1(A_30, B_31, C_32)=A_30 | ~v1_funct_2(C_32, A_30, B_31) | ~r2_hidden(C_32, k1_funct_2(A_30, B_31)))), inference(resolution, [status(thm)], [c_56, c_3046])).
% 10.31/3.66  tff(c_4901, plain, (![B_1636, A_1637, C_1638]: (B_1636='#skF_2' | k1_relset_1(A_1637, B_1636, C_1638)=A_1637 | ~v1_funct_2(C_1638, A_1637, B_1636) | ~r2_hidden(C_1638, k1_funct_2(A_1637, B_1636)))), inference(demodulation, [status(thm), theory('equality')], [c_4599, c_3060])).
% 10.31/3.66  tff(c_4911, plain, ('#skF_2'='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_4901])).
% 10.31/3.66  tff(c_4916, plain, ('#skF_2'='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_1440, c_4911])).
% 10.31/3.66  tff(c_4917, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_148, c_4916])).
% 10.31/3.66  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.31/3.66  tff(c_4704, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4599, c_6])).
% 10.31/3.66  tff(c_4933, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4917, c_4704])).
% 10.31/3.66  tff(c_4942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_4933])).
% 10.31/3.66  tff(c_4944, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4589])).
% 10.31/3.66  tff(c_26, plain, (![A_16, B_17]: (k1_relat_1(k2_zfmisc_1(A_16, B_17))=A_16 | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.31/3.66  tff(c_952, plain, (![A_527, B_528]: (r1_tarski(k1_relat_1(A_527), k1_relat_1(B_528)) | ~r1_tarski(A_527, B_528) | ~v1_relat_1(B_528) | ~v1_relat_1(A_527))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.31/3.66  tff(c_958, plain, (![A_527, A_16, B_17]: (r1_tarski(k1_relat_1(A_527), A_16) | ~r1_tarski(A_527, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_527) | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_26, c_952])).
% 10.31/3.66  tff(c_5321, plain, (![A_1648, A_1649, B_1650]: (r1_tarski(k1_relat_1(A_1648), A_1649) | ~r1_tarski(A_1648, k2_zfmisc_1(A_1649, B_1650)) | ~v1_relat_1(A_1648) | k1_xboole_0=B_1650 | k1_xboole_0=A_1649)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_958])).
% 10.31/3.66  tff(c_5331, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_656, c_5321])).
% 10.31/3.66  tff(c_5354, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5331])).
% 10.31/3.66  tff(c_5355, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4944, c_5354])).
% 10.31/3.66  tff(c_5365, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5355])).
% 10.31/3.66  tff(c_5475, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5365, c_6])).
% 10.31/3.66  tff(c_5477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_5475])).
% 10.31/3.66  tff(c_5479, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5355])).
% 10.31/3.66  tff(c_6993, plain, (![B_1661, A_1662, C_1663]: (k1_xboole_0=B_1661 | k1_relset_1(A_1662, B_1661, C_1663)=A_1662 | ~v1_funct_2(C_1663, A_1662, B_1661) | ~r2_hidden(C_1663, k1_funct_2(A_1662, B_1661)))), inference(resolution, [status(thm)], [c_56, c_3046])).
% 10.31/3.66  tff(c_7072, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_6993])).
% 10.31/3.66  tff(c_7089, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_443, c_1440, c_7072])).
% 10.31/3.66  tff(c_7091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_5479, c_7089])).
% 10.31/3.66  tff(c_7093, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_183])).
% 10.31/3.66  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.31/3.66  tff(c_7101, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_7093, c_8])).
% 10.31/3.66  tff(c_7092, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_183])).
% 10.31/3.66  tff(c_7097, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_7092, c_8])).
% 10.31/3.66  tff(c_7119, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7101, c_7097])).
% 10.31/3.66  tff(c_7128, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7119, c_66])).
% 10.31/3.66  tff(c_121, plain, (![A_46, B_47]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_46, B_47)), B_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.31/3.66  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.31/3.66  tff(c_126, plain, (![A_46]: (k2_relat_1(k2_zfmisc_1(A_46, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_121, c_12])).
% 10.31/3.66  tff(c_7106, plain, (![A_46]: (k2_relat_1(k2_zfmisc_1(A_46, '#skF_2'))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7097, c_7097, c_126])).
% 10.31/3.66  tff(c_7188, plain, (![A_46]: (k2_relat_1(k2_zfmisc_1(A_46, '#skF_3'))='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7119, c_7119, c_7106])).
% 10.31/3.66  tff(c_160, plain, (![A_53]: (k2_relat_1(A_53)!=k1_xboole_0 | k1_xboole_0=A_53 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.31/3.66  tff(c_167, plain, (![A_10, B_11]: (k2_relat_1(k2_zfmisc_1(A_10, B_11))!=k1_xboole_0 | k2_zfmisc_1(A_10, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_160])).
% 10.31/3.66  tff(c_7480, plain, (![A_1695, B_1696]: (k2_relat_1(k2_zfmisc_1(A_1695, B_1696))!='#skF_3' | k2_zfmisc_1(A_1695, B_1696)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7101, c_7101, c_167])).
% 10.31/3.66  tff(c_7495, plain, (![A_1697]: (k2_zfmisc_1(A_1697, '#skF_3')='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7188, c_7480])).
% 10.31/3.66  tff(c_7634, plain, (![C_1700, A_1701]: (m1_subset_1(C_1700, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_1700, k1_funct_2(A_1701, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7495, c_56])).
% 10.31/3.66  tff(c_7650, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_7128, c_7634])).
% 10.31/3.66  tff(c_7655, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_7650, c_14])).
% 10.31/3.66  tff(c_7108, plain, (![A_7]: (A_7='#skF_2' | ~r1_tarski(A_7, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7097, c_7097, c_12])).
% 10.31/3.66  tff(c_7221, plain, (![A_7]: (A_7='#skF_3' | ~r1_tarski(A_7, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7119, c_7119, c_7108])).
% 10.31/3.66  tff(c_7659, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_7655, c_7221])).
% 10.31/3.66  tff(c_7126, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7119, c_148])).
% 10.31/3.66  tff(c_7686, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7659, c_7126])).
% 10.31/3.66  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.31/3.66  tff(c_7112, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7097, c_7097, c_34])).
% 10.31/3.66  tff(c_7134, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7119, c_7119, c_7112])).
% 10.31/3.66  tff(c_7690, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7659, c_7659, c_7134])).
% 10.31/3.66  tff(c_7727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7686, c_7690])).
% 10.31/3.66  tff(c_7729, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 10.31/3.66  tff(c_138, plain, (![A_49]: (k1_relat_1(A_49)!=k1_xboole_0 | k1_xboole_0=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.31/3.66  tff(c_146, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_70, c_138])).
% 10.31/3.66  tff(c_147, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_146])).
% 10.31/3.66  tff(c_7734, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7729, c_147])).
% 10.31/3.66  tff(c_7762, plain, (![A_1713, B_1714]: (v1_xboole_0(k1_funct_2(A_1713, B_1714)) | ~v1_xboole_0(B_1714) | v1_xboole_0(A_1713))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.31/3.66  tff(c_7769, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_7762, c_91])).
% 10.31/3.66  tff(c_7795, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_7769])).
% 10.31/3.66  tff(c_7728, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 10.31/3.66  tff(c_8364, plain, (![C_2140, A_2141, B_2142]: (m1_subset_1(C_2140, k1_zfmisc_1(k2_zfmisc_1(A_2141, B_2142))) | ~r2_hidden(C_2140, k1_funct_2(A_2141, B_2142)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.31/3.66  tff(c_8498, plain, (![C_2150, A_2151, B_2152]: (r1_tarski(C_2150, k2_zfmisc_1(A_2151, B_2152)) | ~r2_hidden(C_2150, k1_funct_2(A_2151, B_2152)))), inference(resolution, [status(thm)], [c_8364, c_14])).
% 10.31/3.66  tff(c_8536, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_66, c_8498])).
% 10.31/3.66  tff(c_8831, plain, (![A_2178, B_2179]: (r1_tarski(k2_relat_1(A_2178), k2_relat_1(B_2179)) | ~r1_tarski(A_2178, B_2179) | ~v1_relat_1(B_2179) | ~v1_relat_1(A_2178))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.31/3.66  tff(c_8837, plain, (![A_2178, B_17, A_16]: (r1_tarski(k2_relat_1(A_2178), B_17) | ~r1_tarski(A_2178, k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(k2_zfmisc_1(A_16, B_17)) | ~v1_relat_1(A_2178) | k1_xboole_0=B_17 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_24, c_8831])).
% 10.31/3.66  tff(c_10587, plain, (![A_2262, B_2263, A_2264]: (r1_tarski(k2_relat_1(A_2262), B_2263) | ~r1_tarski(A_2262, k2_zfmisc_1(A_2264, B_2263)) | ~v1_relat_1(A_2262) | k1_xboole_0=B_2263 | k1_xboole_0=A_2264)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8837])).
% 10.31/3.66  tff(c_10595, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8536, c_10587])).
% 10.31/3.66  tff(c_10618, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_10595])).
% 10.31/3.66  tff(c_10619, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_7734, c_7728, c_10618])).
% 10.31/3.66  tff(c_10718, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10619, c_6])).
% 10.31/3.66  tff(c_10720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7795, c_10718])).
% 10.31/3.66  tff(c_10721, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_7769])).
% 10.31/3.66  tff(c_10725, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_10721, c_8])).
% 10.31/3.66  tff(c_10729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7734, c_10725])).
% 10.31/3.66  tff(c_10730, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_146])).
% 10.31/3.66  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.31/3.66  tff(c_10737, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_10730, c_10])).
% 10.31/3.66  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.31/3.66  tff(c_10738, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10730, c_10730, c_32])).
% 10.31/3.66  tff(c_10739, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10730, c_10730, c_34])).
% 10.31/3.66  tff(c_10745, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 10.31/3.66  tff(c_10746, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10739, c_10745])).
% 10.31/3.66  tff(c_10740, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10730, c_6])).
% 10.31/3.66  tff(c_11001, plain, (![C_2291, A_2292, B_2293]: (v1_funct_2(C_2291, A_2292, B_2293) | ~r2_hidden(C_2291, k1_funct_2(A_2292, B_2293)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.31/3.66  tff(c_11019, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_11001])).
% 10.31/3.66  tff(c_12274, plain, (![A_2343, B_2344, C_2345]: (k1_relset_1(A_2343, B_2344, C_2345)=k1_relat_1(C_2345) | ~m1_subset_1(C_2345, k1_zfmisc_1(k2_zfmisc_1(A_2343, B_2344))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.31/3.66  tff(c_12636, plain, (![A_2370, B_2371, A_2372]: (k1_relset_1(A_2370, B_2371, A_2372)=k1_relat_1(A_2372) | ~r1_tarski(A_2372, k2_zfmisc_1(A_2370, B_2371)))), inference(resolution, [status(thm)], [c_16, c_12274])).
% 10.31/3.66  tff(c_12653, plain, (![A_2370, B_2371]: (k1_relset_1(A_2370, B_2371, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10737, c_12636])).
% 10.31/3.66  tff(c_12665, plain, (![A_2370, B_2371]: (k1_relset_1(A_2370, B_2371, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10739, c_12653])).
% 10.31/3.66  tff(c_52, plain, (![B_26, A_25, C_27]: (k1_xboole_0=B_26 | k1_relset_1(A_25, B_26, C_27)=A_25 | ~v1_funct_2(C_27, A_25, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 10.31/3.66  tff(c_13808, plain, (![B_3299, A_3300, C_3301]: (B_3299='#skF_4' | k1_relset_1(A_3300, B_3299, C_3301)=A_3300 | ~v1_funct_2(C_3301, A_3300, B_3299) | ~m1_subset_1(C_3301, k1_zfmisc_1(k2_zfmisc_1(A_3300, B_3299))))), inference(demodulation, [status(thm), theory('equality')], [c_10730, c_52])).
% 10.31/3.66  tff(c_19770, plain, (![B_3377, A_3378, C_3379]: (B_3377='#skF_4' | k1_relset_1(A_3378, B_3377, C_3379)=A_3378 | ~v1_funct_2(C_3379, A_3378, B_3377) | ~r2_hidden(C_3379, k1_funct_2(A_3378, B_3377)))), inference(resolution, [status(thm)], [c_56, c_13808])).
% 10.31/3.66  tff(c_19873, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_19770])).
% 10.31/3.66  tff(c_19892, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11019, c_12665, c_19873])).
% 10.31/3.66  tff(c_19893, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_10746, c_19892])).
% 10.31/3.66  tff(c_10846, plain, (![A_2279, B_2280]: (v1_xboole_0(k1_funct_2(A_2279, B_2280)) | ~v1_xboole_0(B_2280) | v1_xboole_0(A_2279))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.31/3.66  tff(c_10854, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_10846, c_91])).
% 10.31/3.66  tff(c_10855, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_10854])).
% 10.31/3.66  tff(c_19917, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19893, c_10855])).
% 10.31/3.66  tff(c_19924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10740, c_19917])).
% 10.31/3.66  tff(c_19925, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_10854])).
% 10.31/3.66  tff(c_10736, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_10730, c_8])).
% 10.31/3.66  tff(c_19929, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_19925, c_10736])).
% 10.31/3.66  tff(c_19933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10746, c_19929])).
% 10.31/3.66  tff(c_19934, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 10.31/3.66  tff(c_19958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10737, c_10738, c_19934])).
% 10.31/3.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.31/3.66  
% 10.31/3.66  Inference rules
% 10.31/3.66  ----------------------
% 10.31/3.66  #Ref     : 0
% 10.31/3.66  #Sup     : 4325
% 10.31/3.66  #Fact    : 28
% 10.31/3.66  #Define  : 0
% 10.31/3.66  #Split   : 33
% 10.31/3.66  #Chain   : 0
% 10.31/3.66  #Close   : 0
% 10.31/3.66  
% 10.31/3.66  Ordering : KBO
% 10.31/3.66  
% 10.31/3.66  Simplification rules
% 10.31/3.66  ----------------------
% 10.31/3.66  #Subsume      : 1209
% 10.31/3.66  #Demod        : 3448
% 10.31/3.66  #Tautology    : 2270
% 10.31/3.66  #SimpNegUnit  : 244
% 10.31/3.66  #BackRed      : 486
% 10.31/3.66  
% 10.31/3.66  #Partial instantiations: 306
% 10.31/3.66  #Strategies tried      : 1
% 10.31/3.66  
% 10.31/3.66  Timing (in seconds)
% 10.31/3.66  ----------------------
% 10.31/3.66  Preprocessing        : 0.34
% 10.31/3.66  Parsing              : 0.18
% 10.31/3.66  CNF conversion       : 0.02
% 10.31/3.66  Main loop            : 2.53
% 10.31/3.66  Inferencing          : 0.74
% 10.31/3.66  Reduction            : 0.77
% 10.31/3.66  Demodulation         : 0.54
% 10.31/3.66  BG Simplification    : 0.08
% 10.31/3.66  Subsumption          : 0.78
% 10.31/3.66  Abstraction          : 0.10
% 10.31/3.66  MUC search           : 0.00
% 10.31/3.66  Cooper               : 0.00
% 10.31/3.66  Total                : 2.94
% 10.31/3.66  Index Insertion      : 0.00
% 10.31/3.66  Index Deletion       : 0.00
% 10.31/3.66  Index Matching       : 0.00
% 10.31/3.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
