%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:40 EST 2020

% Result     : Theorem 15.37s
% Output     : CNFRefutation 15.78s
% Verified   : 
% Statistics : Number of formulae       :  210 (1675 expanded)
%              Number of leaves         :   38 ( 551 expanded)
%              Depth                    :   21
%              Number of atoms          :  392 (5517 expanded)
%              Number of equality atoms :   93 (1846 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_160,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_126,axiom,(
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

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_149,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_149])).

tff(c_155,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_152])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40114,plain,(
    ! [A_1508,B_1509,C_1510] :
      ( k1_relset_1(A_1508,B_1509,C_1510) = k1_relat_1(C_1510)
      | ~ m1_subset_1(C_1510,k1_zfmisc_1(k2_zfmisc_1(A_1508,B_1509))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40128,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_40114])).

tff(c_41022,plain,(
    ! [B_1571,A_1572,C_1573] :
      ( k1_xboole_0 = B_1571
      | k1_relset_1(A_1572,B_1571,C_1573) = A_1572
      | ~ v1_funct_2(C_1573,A_1572,B_1571)
      | ~ m1_subset_1(C_1573,k1_zfmisc_1(k2_zfmisc_1(A_1572,B_1571))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_41031,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_41022])).

tff(c_41046,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_40128,c_41031])).

tff(c_41047,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_41046])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( k1_relat_1(k7_relat_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,k1_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_41064,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_23)) = A_23
      | ~ r1_tarski(A_23,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41047,c_32])).

tff(c_41307,plain,(
    ! [A_1584] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_1584)) = A_1584
      | ~ r1_tarski(A_1584,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_41064])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40936,plain,(
    ! [A_1564,B_1565,C_1566,D_1567] :
      ( k2_partfun1(A_1564,B_1565,C_1566,D_1567) = k7_relat_1(C_1566,D_1567)
      | ~ m1_subset_1(C_1566,k1_zfmisc_1(k2_zfmisc_1(A_1564,B_1565)))
      | ~ v1_funct_1(C_1566) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_40942,plain,(
    ! [D_1567] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1567) = k7_relat_1('#skF_4',D_1567)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_40936])).

tff(c_40955,plain,(
    ! [D_1567] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1567) = k7_relat_1('#skF_4',D_1567) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_40942])).

tff(c_1339,plain,(
    ! [C_167,A_168,B_169] :
      ( v4_relat_1(C_167,A_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1349,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1339])).

tff(c_16024,plain,(
    ! [A_901,B_902,C_903] :
      ( k1_relset_1(A_901,B_902,C_903) = k1_relat_1(C_903)
      | ~ m1_subset_1(C_903,k1_zfmisc_1(k2_zfmisc_1(A_901,B_902))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_16034,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_16024])).

tff(c_17275,plain,(
    ! [B_1001,A_1002,C_1003] :
      ( k1_xboole_0 = B_1001
      | k1_relset_1(A_1002,B_1001,C_1003) = A_1002
      | ~ v1_funct_2(C_1003,A_1002,B_1001)
      | ~ m1_subset_1(C_1003,k1_zfmisc_1(k2_zfmisc_1(A_1002,B_1001))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_17284,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_17275])).

tff(c_17299,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_16034,c_17284])).

tff(c_17300,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_17299])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_17330,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_1',A_10)
      | ~ v4_relat_1('#skF_4',A_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17300,c_16])).

tff(c_17422,plain,(
    ! [A_1006] :
      ( r1_tarski('#skF_1',A_1006)
      | ~ v4_relat_1('#skF_4',A_1006) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_17330])).

tff(c_17430,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1349,c_17422])).

tff(c_16935,plain,(
    ! [D_970,B_971,C_972,A_973] :
      ( m1_subset_1(D_970,k1_zfmisc_1(k2_zfmisc_1(B_971,C_972)))
      | ~ r1_tarski(k1_relat_1(D_970),B_971)
      | ~ m1_subset_1(D_970,k1_zfmisc_1(k2_zfmisc_1(A_973,C_972))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16944,plain,(
    ! [B_974] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_974,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_974) ) ),
    inference(resolution,[status(thm)],[c_68,c_16935])).

tff(c_36,plain,(
    ! [C_27,A_25,B_26] :
      ( v4_relat_1(C_27,A_25)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16970,plain,(
    ! [B_974] :
      ( v4_relat_1('#skF_4',B_974)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_974) ) ),
    inference(resolution,[status(thm)],[c_16944,c_36])).

tff(c_17307,plain,(
    ! [B_974] :
      ( v4_relat_1('#skF_4',B_974)
      | ~ r1_tarski('#skF_1',B_974) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17300,c_16970])).

tff(c_1319,plain,(
    ! [B_164,A_165] :
      ( r1_tarski(k1_relat_1(B_164),A_165)
      | ~ v4_relat_1(B_164,A_165)
      | ~ v1_relat_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1334,plain,(
    ! [A_1,A_165,B_164] :
      ( r1_tarski(A_1,A_165)
      | ~ r1_tarski(A_1,k1_relat_1(B_164))
      | ~ v4_relat_1(B_164,A_165)
      | ~ v1_relat_1(B_164) ) ),
    inference(resolution,[status(thm)],[c_1319,c_2])).

tff(c_17312,plain,(
    ! [A_1,A_165] :
      ( r1_tarski(A_1,A_165)
      | ~ r1_tarski(A_1,'#skF_1')
      | ~ v4_relat_1('#skF_4',A_165)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17300,c_1334])).

tff(c_18031,plain,(
    ! [A_1037,A_1038] :
      ( r1_tarski(A_1037,A_1038)
      | ~ r1_tarski(A_1037,'#skF_1')
      | ~ v4_relat_1('#skF_4',A_1038) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_17312])).

tff(c_18061,plain,(
    ! [A_1039] :
      ( r1_tarski('#skF_3',A_1039)
      | ~ v4_relat_1('#skF_4',A_1039) ) ),
    inference(resolution,[status(thm)],[c_66,c_18031])).

tff(c_18068,plain,(
    ! [B_974] :
      ( r1_tarski('#skF_3',B_974)
      | ~ r1_tarski('#skF_1',B_974) ) ),
    inference(resolution,[status(thm)],[c_17307,c_18061])).

tff(c_1374,plain,(
    ! [C_171,A_172,B_173] :
      ( v4_relat_1(k7_relat_1(C_171,A_172),A_172)
      | ~ v4_relat_1(C_171,B_173)
      | ~ v1_relat_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1376,plain,(
    ! [A_172] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_172),A_172)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1349,c_1374])).

tff(c_1379,plain,(
    ! [A_172] : v4_relat_1(k7_relat_1('#skF_4',A_172),A_172) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1376])).

tff(c_17012,plain,(
    ! [A_976,B_977,C_978,D_979] :
      ( k2_partfun1(A_976,B_977,C_978,D_979) = k7_relat_1(C_978,D_979)
      | ~ m1_subset_1(C_978,k1_zfmisc_1(k2_zfmisc_1(A_976,B_977)))
      | ~ v1_funct_1(C_978) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_17016,plain,(
    ! [D_979] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_979) = k7_relat_1('#skF_4',D_979)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_17012])).

tff(c_17026,plain,(
    ! [D_979] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_979) = k7_relat_1('#skF_4',D_979) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_17016])).

tff(c_17439,plain,(
    ! [A_1007,B_1008,C_1009,D_1010] :
      ( m1_subset_1(k2_partfun1(A_1007,B_1008,C_1009,D_1010),k1_zfmisc_1(k2_zfmisc_1(A_1007,B_1008)))
      | ~ m1_subset_1(C_1009,k1_zfmisc_1(k2_zfmisc_1(A_1007,B_1008)))
      | ~ v1_funct_1(C_1009) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_17468,plain,(
    ! [D_979] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_979),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17026,c_17439])).

tff(c_17497,plain,(
    ! [D_1012] : m1_subset_1(k7_relat_1('#skF_4',D_1012),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_17468])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( v1_relat_1(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_17523,plain,(
    ! [D_1012] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_1012))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_17497,c_12])).

tff(c_17546,plain,(
    ! [D_1012] : v1_relat_1(k7_relat_1('#skF_4',D_1012)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_17523])).

tff(c_17321,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_23)) = A_23
      | ~ r1_tarski(A_23,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17300,c_32])).

tff(c_17792,plain,(
    ! [A_1025] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_1025)) = A_1025
      | ~ r1_tarski(A_1025,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_17321])).

tff(c_17822,plain,(
    ! [A_1025,A_10] :
      ( r1_tarski(A_1025,A_10)
      | ~ v4_relat_1(k7_relat_1('#skF_4',A_1025),A_10)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_1025))
      | ~ r1_tarski(A_1025,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17792,c_16])).

tff(c_18350,plain,(
    ! [A_1071,A_1072] :
      ( r1_tarski(A_1071,A_1072)
      | ~ v4_relat_1(k7_relat_1('#skF_4',A_1071),A_1072)
      | ~ r1_tarski(A_1071,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17546,c_17822])).

tff(c_18384,plain,(
    ! [A_1073] :
      ( r1_tarski(A_1073,A_1073)
      | ~ r1_tarski(A_1073,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1379,c_18350])).

tff(c_18387,plain,
    ( r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_18068,c_18384])).

tff(c_18410,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17430,c_18387])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1380,plain,(
    ! [A_174] : v4_relat_1(k7_relat_1('#skF_4',A_174),A_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_1376])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( k7_relat_1(B_20,A_19) = B_20
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16195,plain,(
    ! [A_911] :
      ( k7_relat_1(k7_relat_1('#skF_4',A_911),A_911) = k7_relat_1('#skF_4',A_911)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_911)) ) ),
    inference(resolution,[status(thm)],[c_1380,c_28])).

tff(c_16204,plain,(
    ! [B_13] :
      ( k7_relat_1(k7_relat_1('#skF_4',B_13),B_13) = k7_relat_1('#skF_4',B_13)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_16195])).

tff(c_16212,plain,(
    ! [B_13] : k7_relat_1(k7_relat_1('#skF_4',B_13),B_13) = k7_relat_1('#skF_4',B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_16204])).

tff(c_17343,plain,(
    ! [A_23] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_23)) = A_23
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_17321])).

tff(c_17542,plain,(
    ! [D_1012] : v4_relat_1(k7_relat_1('#skF_4',D_1012),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17497,c_36])).

tff(c_18467,plain,(
    ! [B_1077] :
      ( r1_tarski(k1_relat_1(B_1077),k1_relat_1(B_1077))
      | ~ v4_relat_1(B_1077,'#skF_1')
      | ~ v1_relat_1(B_1077) ) ),
    inference(resolution,[status(thm)],[c_16,c_18384])).

tff(c_18491,plain,(
    ! [A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_23)),A_23)
      | ~ v4_relat_1(k7_relat_1('#skF_4',A_23),'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_23))
      | ~ r1_tarski(A_23,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17343,c_18467])).

tff(c_18606,plain,(
    ! [A_1079] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_1079)),A_1079)
      | ~ r1_tarski(A_1079,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17546,c_17542,c_18491])).

tff(c_18071,plain,(
    ! [B_1040] :
      ( r1_tarski('#skF_3',B_1040)
      | ~ r1_tarski('#skF_1',B_1040) ) ),
    inference(resolution,[status(thm)],[c_17307,c_18061])).

tff(c_18127,plain,(
    ! [A_1,B_1040] :
      ( r1_tarski(A_1,B_1040)
      | ~ r1_tarski(A_1,'#skF_3')
      | ~ r1_tarski('#skF_1',B_1040) ) ),
    inference(resolution,[status(thm)],[c_18071,c_2])).

tff(c_18619,plain,(
    ! [B_1040] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),B_1040)
      | ~ r1_tarski('#skF_1',B_1040)
      | ~ r1_tarski('#skF_3','#skF_1') ) ),
    inference(resolution,[status(thm)],[c_18606,c_18127])).

tff(c_18822,plain,(
    ! [B_1084] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),B_1084)
      | ~ r1_tarski('#skF_1',B_1084) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_18619])).

tff(c_18381,plain,(
    ! [A_172] :
      ( r1_tarski(A_172,A_172)
      | ~ r1_tarski(A_172,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1379,c_18350])).

tff(c_18825,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_relat_1(k7_relat_1('#skF_4','#skF_3')))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_18822,c_18381])).

tff(c_18881,plain,(
    r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17430,c_18825])).

tff(c_19184,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_3')))
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_17343,c_18881])).

tff(c_19207,plain,(
    r1_tarski('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_19184])).

tff(c_19219,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_19207,c_32])).

tff(c_19236,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17546,c_16212,c_19219])).

tff(c_40,plain,(
    ! [D_34,B_32,C_33,A_31] :
      ( m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(B_32,C_33)))
      | ~ r1_tarski(k1_relat_1(D_34),B_32)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(A_31,C_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24321,plain,(
    ! [B_1205,D_1202,A_1203,C_1204,B_1201] :
      ( m1_subset_1(k2_partfun1(A_1203,B_1205,C_1204,D_1202),k1_zfmisc_1(k2_zfmisc_1(B_1201,B_1205)))
      | ~ r1_tarski(k1_relat_1(k2_partfun1(A_1203,B_1205,C_1204,D_1202)),B_1201)
      | ~ m1_subset_1(C_1204,k1_zfmisc_1(k2_zfmisc_1(A_1203,B_1205)))
      | ~ v1_funct_1(C_1204) ) ),
    inference(resolution,[status(thm)],[c_17439,c_40])).

tff(c_24362,plain,(
    ! [D_979,B_1201] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_979),k1_zfmisc_1(k2_zfmisc_1(B_1201,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_979)),B_1201)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17026,c_24321])).

tff(c_39697,plain,(
    ! [D_1481,B_1482] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_1481),k1_zfmisc_1(k2_zfmisc_1(B_1482,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_1481)),B_1482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_17026,c_24362])).

tff(c_1274,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( v1_funct_1(k2_partfun1(A_149,B_150,C_151,D_152))
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1276,plain,(
    ! [D_152] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_152))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_1274])).

tff(c_1283,plain,(
    ! [D_152] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_152)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1276])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_157,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_1286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1283,c_157])).

tff(c_1287,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1338,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1287])).

tff(c_17028,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17026,c_1338])).

tff(c_39726,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_39697,c_17028])).

tff(c_39797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18410,c_19236,c_39726])).

tff(c_39798,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1287])).

tff(c_40965,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40955,c_39798])).

tff(c_39799,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1287])).

tff(c_40127,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_39799,c_40114])).

tff(c_40958,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40955,c_40955,c_40127])).

tff(c_40964,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40955,c_39799])).

tff(c_41199,plain,(
    ! [B_1577,C_1578,A_1579] :
      ( k1_xboole_0 = B_1577
      | v1_funct_2(C_1578,A_1579,B_1577)
      | k1_relset_1(A_1579,B_1577,C_1578) != A_1579
      | ~ m1_subset_1(C_1578,k1_zfmisc_1(k2_zfmisc_1(A_1579,B_1577))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_41205,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_40964,c_41199])).

tff(c_41219,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40958,c_41205])).

tff(c_41220,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40965,c_77,c_41219])).

tff(c_41313,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_41307,c_41220])).

tff(c_41348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_41313])).

tff(c_41349,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41369,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41349,c_41349,c_10])).

tff(c_41386,plain,(
    ! [A_1587,B_1588] : v1_relat_1(k2_zfmisc_1(A_1587,B_1588)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41388,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_41369,c_41386])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41361,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41349,c_41349,c_8])).

tff(c_41350,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_41355,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41349,c_41350])).

tff(c_41385,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41361,c_41355,c_68])).

tff(c_42135,plain,(
    ! [B_1686,A_1687] :
      ( v1_relat_1(B_1686)
      | ~ m1_subset_1(B_1686,k1_zfmisc_1(A_1687))
      | ~ v1_relat_1(A_1687) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_42138,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_41385,c_42135])).

tff(c_42141,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41388,c_42138])).

tff(c_42149,plain,(
    ! [C_1691,A_1692,B_1693] :
      ( v4_relat_1(C_1691,A_1692)
      | ~ m1_subset_1(C_1691,k1_zfmisc_1(k2_zfmisc_1(A_1692,B_1693))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42162,plain,(
    ! [C_1695,A_1696] :
      ( v4_relat_1(C_1695,A_1696)
      | ~ m1_subset_1(C_1695,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41361,c_42149])).

tff(c_42165,plain,(
    ! [A_1696] : v4_relat_1('#skF_4',A_1696) ),
    inference(resolution,[status(thm)],[c_41385,c_42162])).

tff(c_42168,plain,(
    ! [B_1698,A_1699] :
      ( k7_relat_1(B_1698,A_1699) = B_1698
      | ~ v4_relat_1(B_1698,A_1699)
      | ~ v1_relat_1(B_1698) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42171,plain,(
    ! [A_1696] :
      ( k7_relat_1('#skF_4',A_1696) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42165,c_42168])).

tff(c_42174,plain,(
    ! [A_1696] : k7_relat_1('#skF_4',A_1696) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42141,c_42171])).

tff(c_44374,plain,(
    ! [A_1914,B_1915,C_1916,D_1917] :
      ( k2_partfun1(A_1914,B_1915,C_1916,D_1917) = k7_relat_1(C_1916,D_1917)
      | ~ m1_subset_1(C_1916,k1_zfmisc_1(k2_zfmisc_1(A_1914,B_1915)))
      | ~ v1_funct_1(C_1916) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_44518,plain,(
    ! [B_1921,C_1922,D_1923] :
      ( k2_partfun1('#skF_1',B_1921,C_1922,D_1923) = k7_relat_1(C_1922,D_1923)
      | ~ m1_subset_1(C_1922,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1922) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41369,c_44374])).

tff(c_44522,plain,(
    ! [B_1921,D_1923] :
      ( k2_partfun1('#skF_1',B_1921,'#skF_4',D_1923) = k7_relat_1('#skF_4',D_1923)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41385,c_44518])).

tff(c_44527,plain,(
    ! [B_1921,D_1923] : k2_partfun1('#skF_1',B_1921,'#skF_4',D_1923) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_42174,c_44522])).

tff(c_42107,plain,(
    ! [A_1677,B_1678,C_1679,D_1680] :
      ( v1_funct_1(k2_partfun1(A_1677,B_1678,C_1679,D_1680))
      | ~ m1_subset_1(C_1679,k1_zfmisc_1(k2_zfmisc_1(A_1677,B_1678)))
      | ~ v1_funct_1(C_1679) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42112,plain,(
    ! [B_1681,C_1682,D_1683] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_1681,C_1682,D_1683))
      | ~ m1_subset_1(C_1682,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_1682) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41369,c_42107])).

tff(c_42114,plain,(
    ! [B_1681,D_1683] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_1681,'#skF_4',D_1683))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41385,c_42112])).

tff(c_42117,plain,(
    ! [B_1681,D_1683] : v1_funct_1(k2_partfun1('#skF_1',B_1681,'#skF_4',D_1683)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_42114])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41393,plain,(
    ! [A_1589] :
      ( A_1589 = '#skF_1'
      | ~ r1_tarski(A_1589,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41349,c_41349,c_4])).

tff(c_41397,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_66,c_41393])).

tff(c_41434,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41397,c_41355,c_41397,c_41397,c_41355,c_41355,c_41397,c_41361,c_41355,c_41355,c_62])).

tff(c_41435,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_41434])).

tff(c_42120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42117,c_41435])).

tff(c_42121,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_41434])).

tff(c_42156,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_42121])).

tff(c_44529,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44527,c_42156])).

tff(c_44533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41385,c_44529])).

tff(c_44535,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_42121])).

tff(c_44560,plain,
    ( v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44535,c_12])).

tff(c_44564,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41388,c_44560])).

tff(c_42155,plain,(
    ! [C_1691,A_5] :
      ( v4_relat_1(C_1691,A_5)
      | ~ m1_subset_1(C_1691,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41361,c_42149])).

tff(c_44561,plain,(
    ! [A_5] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_5) ),
    inference(resolution,[status(thm)],[c_44535,c_42155])).

tff(c_44547,plain,(
    ! [B_1928,A_1929] :
      ( r1_tarski(k1_relat_1(B_1928),A_1929)
      | ~ v4_relat_1(B_1928,A_1929)
      | ~ v1_relat_1(B_1928) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41392,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41349,c_41349,c_4])).

tff(c_44599,plain,(
    ! [B_1934] :
      ( k1_relat_1(B_1934) = '#skF_1'
      | ~ v4_relat_1(B_1934,'#skF_1')
      | ~ v1_relat_1(B_1934) ) ),
    inference(resolution,[status(thm)],[c_44547,c_41392])).

tff(c_44603,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44561,c_44599])).

tff(c_44610,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44564,c_44603])).

tff(c_44998,plain,(
    ! [A_1969,B_1970,C_1971] :
      ( k1_relset_1(A_1969,B_1970,C_1971) = k1_relat_1(C_1971)
      | ~ m1_subset_1(C_1971,k1_zfmisc_1(k2_zfmisc_1(A_1969,B_1970))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_45058,plain,(
    ! [B_1974,C_1975] :
      ( k1_relset_1('#skF_1',B_1974,C_1975) = k1_relat_1(C_1975)
      | ~ m1_subset_1(C_1975,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41369,c_44998])).

tff(c_45060,plain,(
    ! [B_1974] : k1_relset_1('#skF_1',B_1974,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44535,c_45058])).

tff(c_45064,plain,(
    ! [B_1974] : k1_relset_1('#skF_1',B_1974,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44610,c_45060])).

tff(c_48,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_45276,plain,(
    ! [C_1992,B_1993] :
      ( v1_funct_2(C_1992,'#skF_1',B_1993)
      | k1_relset_1('#skF_1',B_1993,C_1992) != '#skF_1'
      | ~ m1_subset_1(C_1992,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41349,c_41349,c_41349,c_41349,c_74])).

tff(c_45278,plain,(
    ! [B_1993] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_1993)
      | k1_relset_1('#skF_1',B_1993,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_44535,c_45276])).

tff(c_45283,plain,(
    ! [B_1993] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_1993) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45064,c_45278])).

tff(c_44534,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42121])).

tff(c_45303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45283,c_44534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.37/6.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.37/6.59  
% 15.37/6.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.37/6.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.37/6.59  
% 15.37/6.59  %Foreground sorts:
% 15.37/6.59  
% 15.37/6.59  
% 15.37/6.59  %Background operators:
% 15.37/6.59  
% 15.37/6.59  
% 15.37/6.59  %Foreground operators:
% 15.37/6.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.37/6.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.37/6.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 15.37/6.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.37/6.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.37/6.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.37/6.59  tff('#skF_2', type, '#skF_2': $i).
% 15.37/6.59  tff('#skF_3', type, '#skF_3': $i).
% 15.37/6.59  tff('#skF_1', type, '#skF_1': $i).
% 15.37/6.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.37/6.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.37/6.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.37/6.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.37/6.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.37/6.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.37/6.59  tff('#skF_4', type, '#skF_4': $i).
% 15.37/6.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.37/6.59  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.37/6.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.37/6.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.37/6.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.37/6.59  
% 15.78/6.65  tff(f_160, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 15.78/6.65  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.78/6.65  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.78/6.65  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.78/6.65  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 15.78/6.65  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 15.78/6.65  tff(f_140, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 15.78/6.65  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 15.78/6.65  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 15.78/6.65  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 15.78/6.65  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 15.78/6.65  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 15.78/6.65  tff(f_134, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 15.78/6.65  tff(f_58, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 15.78/6.65  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 15.78/6.65  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.78/6.65  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 15.78/6.65  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.78/6.65  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.78/6.65  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.78/6.65  tff(c_149, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.78/6.65  tff(c_152, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_149])).
% 15.78/6.65  tff(c_155, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_152])).
% 15.78/6.65  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.78/6.65  tff(c_77, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 15.78/6.65  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.78/6.65  tff(c_40114, plain, (![A_1508, B_1509, C_1510]: (k1_relset_1(A_1508, B_1509, C_1510)=k1_relat_1(C_1510) | ~m1_subset_1(C_1510, k1_zfmisc_1(k2_zfmisc_1(A_1508, B_1509))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.78/6.65  tff(c_40128, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_40114])).
% 15.78/6.65  tff(c_41022, plain, (![B_1571, A_1572, C_1573]: (k1_xboole_0=B_1571 | k1_relset_1(A_1572, B_1571, C_1573)=A_1572 | ~v1_funct_2(C_1573, A_1572, B_1571) | ~m1_subset_1(C_1573, k1_zfmisc_1(k2_zfmisc_1(A_1572, B_1571))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.78/6.65  tff(c_41031, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_41022])).
% 15.78/6.65  tff(c_41046, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_40128, c_41031])).
% 15.78/6.65  tff(c_41047, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_41046])).
% 15.78/6.65  tff(c_32, plain, (![B_24, A_23]: (k1_relat_1(k7_relat_1(B_24, A_23))=A_23 | ~r1_tarski(A_23, k1_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.78/6.65  tff(c_41064, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_4', A_23))=A_23 | ~r1_tarski(A_23, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_41047, c_32])).
% 15.78/6.65  tff(c_41307, plain, (![A_1584]: (k1_relat_1(k7_relat_1('#skF_4', A_1584))=A_1584 | ~r1_tarski(A_1584, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_41064])).
% 15.78/6.65  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.78/6.65  tff(c_40936, plain, (![A_1564, B_1565, C_1566, D_1567]: (k2_partfun1(A_1564, B_1565, C_1566, D_1567)=k7_relat_1(C_1566, D_1567) | ~m1_subset_1(C_1566, k1_zfmisc_1(k2_zfmisc_1(A_1564, B_1565))) | ~v1_funct_1(C_1566))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.78/6.65  tff(c_40942, plain, (![D_1567]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1567)=k7_relat_1('#skF_4', D_1567) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_40936])).
% 15.78/6.65  tff(c_40955, plain, (![D_1567]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1567)=k7_relat_1('#skF_4', D_1567))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_40942])).
% 15.78/6.65  tff(c_1339, plain, (![C_167, A_168, B_169]: (v4_relat_1(C_167, A_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.78/6.65  tff(c_1349, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_1339])).
% 15.78/6.65  tff(c_16024, plain, (![A_901, B_902, C_903]: (k1_relset_1(A_901, B_902, C_903)=k1_relat_1(C_903) | ~m1_subset_1(C_903, k1_zfmisc_1(k2_zfmisc_1(A_901, B_902))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.78/6.65  tff(c_16034, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_16024])).
% 15.78/6.65  tff(c_17275, plain, (![B_1001, A_1002, C_1003]: (k1_xboole_0=B_1001 | k1_relset_1(A_1002, B_1001, C_1003)=A_1002 | ~v1_funct_2(C_1003, A_1002, B_1001) | ~m1_subset_1(C_1003, k1_zfmisc_1(k2_zfmisc_1(A_1002, B_1001))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.78/6.65  tff(c_17284, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_17275])).
% 15.78/6.65  tff(c_17299, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_16034, c_17284])).
% 15.78/6.65  tff(c_17300, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_17299])).
% 15.78/6.65  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.78/6.65  tff(c_17330, plain, (![A_10]: (r1_tarski('#skF_1', A_10) | ~v4_relat_1('#skF_4', A_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17300, c_16])).
% 15.78/6.65  tff(c_17422, plain, (![A_1006]: (r1_tarski('#skF_1', A_1006) | ~v4_relat_1('#skF_4', A_1006))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_17330])).
% 15.78/6.65  tff(c_17430, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1349, c_17422])).
% 15.78/6.65  tff(c_16935, plain, (![D_970, B_971, C_972, A_973]: (m1_subset_1(D_970, k1_zfmisc_1(k2_zfmisc_1(B_971, C_972))) | ~r1_tarski(k1_relat_1(D_970), B_971) | ~m1_subset_1(D_970, k1_zfmisc_1(k2_zfmisc_1(A_973, C_972))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.78/6.65  tff(c_16944, plain, (![B_974]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_974, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_974))), inference(resolution, [status(thm)], [c_68, c_16935])).
% 15.78/6.65  tff(c_36, plain, (![C_27, A_25, B_26]: (v4_relat_1(C_27, A_25) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.78/6.65  tff(c_16970, plain, (![B_974]: (v4_relat_1('#skF_4', B_974) | ~r1_tarski(k1_relat_1('#skF_4'), B_974))), inference(resolution, [status(thm)], [c_16944, c_36])).
% 15.78/6.65  tff(c_17307, plain, (![B_974]: (v4_relat_1('#skF_4', B_974) | ~r1_tarski('#skF_1', B_974))), inference(demodulation, [status(thm), theory('equality')], [c_17300, c_16970])).
% 15.78/6.65  tff(c_1319, plain, (![B_164, A_165]: (r1_tarski(k1_relat_1(B_164), A_165) | ~v4_relat_1(B_164, A_165) | ~v1_relat_1(B_164))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.78/6.65  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.78/6.65  tff(c_1334, plain, (![A_1, A_165, B_164]: (r1_tarski(A_1, A_165) | ~r1_tarski(A_1, k1_relat_1(B_164)) | ~v4_relat_1(B_164, A_165) | ~v1_relat_1(B_164))), inference(resolution, [status(thm)], [c_1319, c_2])).
% 15.78/6.65  tff(c_17312, plain, (![A_1, A_165]: (r1_tarski(A_1, A_165) | ~r1_tarski(A_1, '#skF_1') | ~v4_relat_1('#skF_4', A_165) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17300, c_1334])).
% 15.78/6.65  tff(c_18031, plain, (![A_1037, A_1038]: (r1_tarski(A_1037, A_1038) | ~r1_tarski(A_1037, '#skF_1') | ~v4_relat_1('#skF_4', A_1038))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_17312])).
% 15.78/6.65  tff(c_18061, plain, (![A_1039]: (r1_tarski('#skF_3', A_1039) | ~v4_relat_1('#skF_4', A_1039))), inference(resolution, [status(thm)], [c_66, c_18031])).
% 15.78/6.65  tff(c_18068, plain, (![B_974]: (r1_tarski('#skF_3', B_974) | ~r1_tarski('#skF_1', B_974))), inference(resolution, [status(thm)], [c_17307, c_18061])).
% 15.78/6.65  tff(c_1374, plain, (![C_171, A_172, B_173]: (v4_relat_1(k7_relat_1(C_171, A_172), A_172) | ~v4_relat_1(C_171, B_173) | ~v1_relat_1(C_171))), inference(cnfTransformation, [status(thm)], [f_68])).
% 15.78/6.65  tff(c_1376, plain, (![A_172]: (v4_relat_1(k7_relat_1('#skF_4', A_172), A_172) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1349, c_1374])).
% 15.78/6.65  tff(c_1379, plain, (![A_172]: (v4_relat_1(k7_relat_1('#skF_4', A_172), A_172))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1376])).
% 15.78/6.65  tff(c_17012, plain, (![A_976, B_977, C_978, D_979]: (k2_partfun1(A_976, B_977, C_978, D_979)=k7_relat_1(C_978, D_979) | ~m1_subset_1(C_978, k1_zfmisc_1(k2_zfmisc_1(A_976, B_977))) | ~v1_funct_1(C_978))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.78/6.65  tff(c_17016, plain, (![D_979]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_979)=k7_relat_1('#skF_4', D_979) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_17012])).
% 15.78/6.65  tff(c_17026, plain, (![D_979]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_979)=k7_relat_1('#skF_4', D_979))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_17016])).
% 15.78/6.65  tff(c_17439, plain, (![A_1007, B_1008, C_1009, D_1010]: (m1_subset_1(k2_partfun1(A_1007, B_1008, C_1009, D_1010), k1_zfmisc_1(k2_zfmisc_1(A_1007, B_1008))) | ~m1_subset_1(C_1009, k1_zfmisc_1(k2_zfmisc_1(A_1007, B_1008))) | ~v1_funct_1(C_1009))), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.78/6.65  tff(c_17468, plain, (![D_979]: (m1_subset_1(k7_relat_1('#skF_4', D_979), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17026, c_17439])).
% 15.78/6.65  tff(c_17497, plain, (![D_1012]: (m1_subset_1(k7_relat_1('#skF_4', D_1012), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_17468])).
% 15.78/6.65  tff(c_12, plain, (![B_9, A_7]: (v1_relat_1(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.78/6.65  tff(c_17523, plain, (![D_1012]: (v1_relat_1(k7_relat_1('#skF_4', D_1012)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_17497, c_12])).
% 15.78/6.65  tff(c_17546, plain, (![D_1012]: (v1_relat_1(k7_relat_1('#skF_4', D_1012)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_17523])).
% 15.78/6.65  tff(c_17321, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_4', A_23))=A_23 | ~r1_tarski(A_23, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17300, c_32])).
% 15.78/6.65  tff(c_17792, plain, (![A_1025]: (k1_relat_1(k7_relat_1('#skF_4', A_1025))=A_1025 | ~r1_tarski(A_1025, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_17321])).
% 15.78/6.65  tff(c_17822, plain, (![A_1025, A_10]: (r1_tarski(A_1025, A_10) | ~v4_relat_1(k7_relat_1('#skF_4', A_1025), A_10) | ~v1_relat_1(k7_relat_1('#skF_4', A_1025)) | ~r1_tarski(A_1025, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_17792, c_16])).
% 15.78/6.65  tff(c_18350, plain, (![A_1071, A_1072]: (r1_tarski(A_1071, A_1072) | ~v4_relat_1(k7_relat_1('#skF_4', A_1071), A_1072) | ~r1_tarski(A_1071, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17546, c_17822])).
% 15.78/6.65  tff(c_18384, plain, (![A_1073]: (r1_tarski(A_1073, A_1073) | ~r1_tarski(A_1073, '#skF_1'))), inference(resolution, [status(thm)], [c_1379, c_18350])).
% 15.78/6.65  tff(c_18387, plain, (r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_18068, c_18384])).
% 15.78/6.65  tff(c_18410, plain, (r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17430, c_18387])).
% 15.78/6.65  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 15.78/6.65  tff(c_1380, plain, (![A_174]: (v4_relat_1(k7_relat_1('#skF_4', A_174), A_174))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_1376])).
% 15.78/6.65  tff(c_28, plain, (![B_20, A_19]: (k7_relat_1(B_20, A_19)=B_20 | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.78/6.65  tff(c_16195, plain, (![A_911]: (k7_relat_1(k7_relat_1('#skF_4', A_911), A_911)=k7_relat_1('#skF_4', A_911) | ~v1_relat_1(k7_relat_1('#skF_4', A_911)))), inference(resolution, [status(thm)], [c_1380, c_28])).
% 15.78/6.65  tff(c_16204, plain, (![B_13]: (k7_relat_1(k7_relat_1('#skF_4', B_13), B_13)=k7_relat_1('#skF_4', B_13) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_16195])).
% 15.78/6.65  tff(c_16212, plain, (![B_13]: (k7_relat_1(k7_relat_1('#skF_4', B_13), B_13)=k7_relat_1('#skF_4', B_13))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_16204])).
% 15.78/6.65  tff(c_17343, plain, (![A_23]: (k1_relat_1(k7_relat_1('#skF_4', A_23))=A_23 | ~r1_tarski(A_23, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_17321])).
% 15.78/6.65  tff(c_17542, plain, (![D_1012]: (v4_relat_1(k7_relat_1('#skF_4', D_1012), '#skF_1'))), inference(resolution, [status(thm)], [c_17497, c_36])).
% 15.78/6.65  tff(c_18467, plain, (![B_1077]: (r1_tarski(k1_relat_1(B_1077), k1_relat_1(B_1077)) | ~v4_relat_1(B_1077, '#skF_1') | ~v1_relat_1(B_1077))), inference(resolution, [status(thm)], [c_16, c_18384])).
% 15.78/6.65  tff(c_18491, plain, (![A_23]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_23)), A_23) | ~v4_relat_1(k7_relat_1('#skF_4', A_23), '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_4', A_23)) | ~r1_tarski(A_23, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_17343, c_18467])).
% 15.78/6.65  tff(c_18606, plain, (![A_1079]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_1079)), A_1079) | ~r1_tarski(A_1079, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_17546, c_17542, c_18491])).
% 15.78/6.65  tff(c_18071, plain, (![B_1040]: (r1_tarski('#skF_3', B_1040) | ~r1_tarski('#skF_1', B_1040))), inference(resolution, [status(thm)], [c_17307, c_18061])).
% 15.78/6.65  tff(c_18127, plain, (![A_1, B_1040]: (r1_tarski(A_1, B_1040) | ~r1_tarski(A_1, '#skF_3') | ~r1_tarski('#skF_1', B_1040))), inference(resolution, [status(thm)], [c_18071, c_2])).
% 15.78/6.65  tff(c_18619, plain, (![B_1040]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), B_1040) | ~r1_tarski('#skF_1', B_1040) | ~r1_tarski('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_18606, c_18127])).
% 15.78/6.65  tff(c_18822, plain, (![B_1084]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), B_1084) | ~r1_tarski('#skF_1', B_1084))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_18619])).
% 15.78/6.65  tff(c_18381, plain, (![A_172]: (r1_tarski(A_172, A_172) | ~r1_tarski(A_172, '#skF_1'))), inference(resolution, [status(thm)], [c_1379, c_18350])).
% 15.78/6.65  tff(c_18825, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))) | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_18822, c_18381])).
% 15.78/6.65  tff(c_18881, plain, (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17430, c_18825])).
% 15.78/6.65  tff(c_19184, plain, (r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))) | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_17343, c_18881])).
% 15.78/6.65  tff(c_19207, plain, (r1_tarski('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_19184])).
% 15.78/6.65  tff(c_19219, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_3'))='#skF_3' | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_19207, c_32])).
% 15.78/6.65  tff(c_19236, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17546, c_16212, c_19219])).
% 15.78/6.65  tff(c_40, plain, (![D_34, B_32, C_33, A_31]: (m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(B_32, C_33))) | ~r1_tarski(k1_relat_1(D_34), B_32) | ~m1_subset_1(D_34, k1_zfmisc_1(k2_zfmisc_1(A_31, C_33))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 15.78/6.65  tff(c_24321, plain, (![B_1205, D_1202, A_1203, C_1204, B_1201]: (m1_subset_1(k2_partfun1(A_1203, B_1205, C_1204, D_1202), k1_zfmisc_1(k2_zfmisc_1(B_1201, B_1205))) | ~r1_tarski(k1_relat_1(k2_partfun1(A_1203, B_1205, C_1204, D_1202)), B_1201) | ~m1_subset_1(C_1204, k1_zfmisc_1(k2_zfmisc_1(A_1203, B_1205))) | ~v1_funct_1(C_1204))), inference(resolution, [status(thm)], [c_17439, c_40])).
% 15.78/6.65  tff(c_24362, plain, (![D_979, B_1201]: (m1_subset_1(k7_relat_1('#skF_4', D_979), k1_zfmisc_1(k2_zfmisc_1(B_1201, '#skF_2'))) | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_979)), B_1201) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17026, c_24321])).
% 15.78/6.65  tff(c_39697, plain, (![D_1481, B_1482]: (m1_subset_1(k7_relat_1('#skF_4', D_1481), k1_zfmisc_1(k2_zfmisc_1(B_1482, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_1481)), B_1482))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_17026, c_24362])).
% 15.78/6.65  tff(c_1274, plain, (![A_149, B_150, C_151, D_152]: (v1_funct_1(k2_partfun1(A_149, B_150, C_151, D_152)) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(C_151))), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.78/6.65  tff(c_1276, plain, (![D_152]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_152)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1274])).
% 15.78/6.65  tff(c_1283, plain, (![D_152]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_152)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1276])).
% 15.78/6.65  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 15.78/6.65  tff(c_157, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 15.78/6.65  tff(c_1286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1283, c_157])).
% 15.78/6.65  tff(c_1287, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 15.78/6.65  tff(c_1338, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1287])).
% 15.78/6.65  tff(c_17028, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_17026, c_1338])).
% 15.78/6.65  tff(c_39726, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_39697, c_17028])).
% 15.78/6.65  tff(c_39797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18410, c_19236, c_39726])).
% 15.78/6.65  tff(c_39798, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1287])).
% 15.78/6.65  tff(c_40965, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40955, c_39798])).
% 15.78/6.65  tff(c_39799, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1287])).
% 15.78/6.65  tff(c_40127, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_39799, c_40114])).
% 15.78/6.65  tff(c_40958, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40955, c_40955, c_40127])).
% 15.78/6.65  tff(c_40964, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40955, c_39799])).
% 15.78/6.65  tff(c_41199, plain, (![B_1577, C_1578, A_1579]: (k1_xboole_0=B_1577 | v1_funct_2(C_1578, A_1579, B_1577) | k1_relset_1(A_1579, B_1577, C_1578)!=A_1579 | ~m1_subset_1(C_1578, k1_zfmisc_1(k2_zfmisc_1(A_1579, B_1577))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.78/6.65  tff(c_41205, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_40964, c_41199])).
% 15.78/6.65  tff(c_41219, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40958, c_41205])).
% 15.78/6.65  tff(c_41220, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40965, c_77, c_41219])).
% 15.78/6.65  tff(c_41313, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_41307, c_41220])).
% 15.78/6.65  tff(c_41348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_41313])).
% 15.78/6.65  tff(c_41349, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 15.78/6.65  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.78/6.65  tff(c_41369, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41349, c_41349, c_10])).
% 15.78/6.65  tff(c_41386, plain, (![A_1587, B_1588]: (v1_relat_1(k2_zfmisc_1(A_1587, B_1588)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.78/6.65  tff(c_41388, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_41369, c_41386])).
% 15.78/6.65  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.78/6.65  tff(c_41361, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_41349, c_41349, c_8])).
% 15.78/6.65  tff(c_41350, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 15.78/6.65  tff(c_41355, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41349, c_41350])).
% 15.78/6.65  tff(c_41385, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_41361, c_41355, c_68])).
% 15.78/6.65  tff(c_42135, plain, (![B_1686, A_1687]: (v1_relat_1(B_1686) | ~m1_subset_1(B_1686, k1_zfmisc_1(A_1687)) | ~v1_relat_1(A_1687))), inference(cnfTransformation, [status(thm)], [f_48])).
% 15.78/6.65  tff(c_42138, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_41385, c_42135])).
% 15.78/6.65  tff(c_42141, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41388, c_42138])).
% 15.78/6.65  tff(c_42149, plain, (![C_1691, A_1692, B_1693]: (v4_relat_1(C_1691, A_1692) | ~m1_subset_1(C_1691, k1_zfmisc_1(k2_zfmisc_1(A_1692, B_1693))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.78/6.65  tff(c_42162, plain, (![C_1695, A_1696]: (v4_relat_1(C_1695, A_1696) | ~m1_subset_1(C_1695, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41361, c_42149])).
% 15.78/6.65  tff(c_42165, plain, (![A_1696]: (v4_relat_1('#skF_4', A_1696))), inference(resolution, [status(thm)], [c_41385, c_42162])).
% 15.78/6.65  tff(c_42168, plain, (![B_1698, A_1699]: (k7_relat_1(B_1698, A_1699)=B_1698 | ~v4_relat_1(B_1698, A_1699) | ~v1_relat_1(B_1698))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.78/6.65  tff(c_42171, plain, (![A_1696]: (k7_relat_1('#skF_4', A_1696)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_42165, c_42168])).
% 15.78/6.65  tff(c_42174, plain, (![A_1696]: (k7_relat_1('#skF_4', A_1696)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42141, c_42171])).
% 15.78/6.65  tff(c_44374, plain, (![A_1914, B_1915, C_1916, D_1917]: (k2_partfun1(A_1914, B_1915, C_1916, D_1917)=k7_relat_1(C_1916, D_1917) | ~m1_subset_1(C_1916, k1_zfmisc_1(k2_zfmisc_1(A_1914, B_1915))) | ~v1_funct_1(C_1916))), inference(cnfTransformation, [status(thm)], [f_140])).
% 15.78/6.65  tff(c_44518, plain, (![B_1921, C_1922, D_1923]: (k2_partfun1('#skF_1', B_1921, C_1922, D_1923)=k7_relat_1(C_1922, D_1923) | ~m1_subset_1(C_1922, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1922))), inference(superposition, [status(thm), theory('equality')], [c_41369, c_44374])).
% 15.78/6.65  tff(c_44522, plain, (![B_1921, D_1923]: (k2_partfun1('#skF_1', B_1921, '#skF_4', D_1923)=k7_relat_1('#skF_4', D_1923) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_41385, c_44518])).
% 15.78/6.65  tff(c_44527, plain, (![B_1921, D_1923]: (k2_partfun1('#skF_1', B_1921, '#skF_4', D_1923)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_42174, c_44522])).
% 15.78/6.65  tff(c_42107, plain, (![A_1677, B_1678, C_1679, D_1680]: (v1_funct_1(k2_partfun1(A_1677, B_1678, C_1679, D_1680)) | ~m1_subset_1(C_1679, k1_zfmisc_1(k2_zfmisc_1(A_1677, B_1678))) | ~v1_funct_1(C_1679))), inference(cnfTransformation, [status(thm)], [f_134])).
% 15.78/6.65  tff(c_42112, plain, (![B_1681, C_1682, D_1683]: (v1_funct_1(k2_partfun1('#skF_1', B_1681, C_1682, D_1683)) | ~m1_subset_1(C_1682, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_1682))), inference(superposition, [status(thm), theory('equality')], [c_41369, c_42107])).
% 15.78/6.65  tff(c_42114, plain, (![B_1681, D_1683]: (v1_funct_1(k2_partfun1('#skF_1', B_1681, '#skF_4', D_1683)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_41385, c_42112])).
% 15.78/6.65  tff(c_42117, plain, (![B_1681, D_1683]: (v1_funct_1(k2_partfun1('#skF_1', B_1681, '#skF_4', D_1683)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_42114])).
% 15.78/6.65  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.78/6.65  tff(c_41393, plain, (![A_1589]: (A_1589='#skF_1' | ~r1_tarski(A_1589, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_41349, c_41349, c_4])).
% 15.78/6.65  tff(c_41397, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_66, c_41393])).
% 15.78/6.65  tff(c_41434, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_41397, c_41355, c_41397, c_41397, c_41355, c_41355, c_41397, c_41361, c_41355, c_41355, c_62])).
% 15.78/6.65  tff(c_41435, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_41434])).
% 15.78/6.65  tff(c_42120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42117, c_41435])).
% 15.78/6.65  tff(c_42121, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_41434])).
% 15.78/6.65  tff(c_42156, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_42121])).
% 15.78/6.65  tff(c_44529, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44527, c_42156])).
% 15.78/6.65  tff(c_44533, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41385, c_44529])).
% 15.78/6.65  tff(c_44535, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_42121])).
% 15.78/6.65  tff(c_44560, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_44535, c_12])).
% 15.78/6.65  tff(c_44564, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_41388, c_44560])).
% 15.78/6.65  tff(c_42155, plain, (![C_1691, A_5]: (v4_relat_1(C_1691, A_5) | ~m1_subset_1(C_1691, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41361, c_42149])).
% 15.78/6.65  tff(c_44561, plain, (![A_5]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_5))), inference(resolution, [status(thm)], [c_44535, c_42155])).
% 15.78/6.65  tff(c_44547, plain, (![B_1928, A_1929]: (r1_tarski(k1_relat_1(B_1928), A_1929) | ~v4_relat_1(B_1928, A_1929) | ~v1_relat_1(B_1928))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.78/6.65  tff(c_41392, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_41349, c_41349, c_4])).
% 15.78/6.65  tff(c_44599, plain, (![B_1934]: (k1_relat_1(B_1934)='#skF_1' | ~v4_relat_1(B_1934, '#skF_1') | ~v1_relat_1(B_1934))), inference(resolution, [status(thm)], [c_44547, c_41392])).
% 15.78/6.65  tff(c_44603, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_44561, c_44599])).
% 15.78/6.65  tff(c_44610, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44564, c_44603])).
% 15.78/6.65  tff(c_44998, plain, (![A_1969, B_1970, C_1971]: (k1_relset_1(A_1969, B_1970, C_1971)=k1_relat_1(C_1971) | ~m1_subset_1(C_1971, k1_zfmisc_1(k2_zfmisc_1(A_1969, B_1970))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.78/6.65  tff(c_45058, plain, (![B_1974, C_1975]: (k1_relset_1('#skF_1', B_1974, C_1975)=k1_relat_1(C_1975) | ~m1_subset_1(C_1975, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_41369, c_44998])).
% 15.78/6.65  tff(c_45060, plain, (![B_1974]: (k1_relset_1('#skF_1', B_1974, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_44535, c_45058])).
% 15.78/6.65  tff(c_45064, plain, (![B_1974]: (k1_relset_1('#skF_1', B_1974, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44610, c_45060])).
% 15.78/6.65  tff(c_48, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 15.78/6.65  tff(c_74, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 15.78/6.65  tff(c_45276, plain, (![C_1992, B_1993]: (v1_funct_2(C_1992, '#skF_1', B_1993) | k1_relset_1('#skF_1', B_1993, C_1992)!='#skF_1' | ~m1_subset_1(C_1992, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_41349, c_41349, c_41349, c_41349, c_74])).
% 15.78/6.65  tff(c_45278, plain, (![B_1993]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_1993) | k1_relset_1('#skF_1', B_1993, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1')), inference(resolution, [status(thm)], [c_44535, c_45276])).
% 15.78/6.65  tff(c_45283, plain, (![B_1993]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_1993))), inference(demodulation, [status(thm), theory('equality')], [c_45064, c_45278])).
% 15.78/6.65  tff(c_44534, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_42121])).
% 15.78/6.65  tff(c_45303, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45283, c_44534])).
% 15.78/6.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.78/6.65  
% 15.78/6.65  Inference rules
% 15.78/6.65  ----------------------
% 15.78/6.65  #Ref     : 0
% 15.78/6.65  #Sup     : 9625
% 15.78/6.65  #Fact    : 0
% 15.78/6.65  #Define  : 0
% 15.78/6.65  #Split   : 68
% 15.78/6.65  #Chain   : 0
% 15.78/6.65  #Close   : 0
% 15.78/6.65  
% 15.78/6.65  Ordering : KBO
% 15.78/6.65  
% 15.78/6.65  Simplification rules
% 15.78/6.65  ----------------------
% 15.78/6.65  #Subsume      : 2771
% 15.78/6.65  #Demod        : 10817
% 15.78/6.65  #Tautology    : 3548
% 15.78/6.65  #SimpNegUnit  : 292
% 15.78/6.65  #BackRed      : 112
% 15.78/6.65  
% 15.78/6.65  #Partial instantiations: 0
% 15.78/6.65  #Strategies tried      : 1
% 15.78/6.65  
% 15.78/6.65  Timing (in seconds)
% 15.78/6.65  ----------------------
% 15.78/6.65  Preprocessing        : 0.37
% 15.78/6.65  Parsing              : 0.20
% 15.78/6.65  CNF conversion       : 0.02
% 15.78/6.65  Main loop            : 5.40
% 15.78/6.65  Inferencing          : 1.27
% 15.78/6.65  Reduction            : 2.28
% 15.78/6.65  Demodulation         : 1.72
% 15.78/6.65  BG Simplification    : 0.11
% 15.78/6.65  Subsumption          : 1.42
% 15.78/6.65  Abstraction          : 0.17
% 15.78/6.66  MUC search           : 0.00
% 15.78/6.66  Cooper               : 0.00
% 15.78/6.66  Total                : 5.87
% 15.78/6.66  Index Insertion      : 0.00
% 15.78/6.66  Index Deletion       : 0.00
% 15.78/6.66  Index Matching       : 0.00
% 15.78/6.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
