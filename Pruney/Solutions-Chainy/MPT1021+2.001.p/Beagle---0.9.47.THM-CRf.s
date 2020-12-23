%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:59 EST 2020

% Result     : Theorem 22.88s
% Output     : CNFRefutation 23.19s
% Verified   : 
% Statistics : Number of formulae       :  338 (7900 expanded)
%              Number of leaves         :   51 (2608 expanded)
%              Depth                    :   18
%              Number of atoms          :  673 (18545 expanded)
%              Number of equality atoms :  178 (3432 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_195,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_150,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_172,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_170,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_160,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_182,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_65,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_84,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_96383,plain,(
    ! [C_1379,A_1380,B_1381] :
      ( v1_relat_1(C_1379)
      | ~ m1_subset_1(C_1379,k1_zfmisc_1(k2_zfmisc_1(A_1380,B_1381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_96395,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_96383])).

tff(c_90,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_86,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_97145,plain,(
    ! [C_1457,A_1458,B_1459] :
      ( v2_funct_1(C_1457)
      | ~ v3_funct_2(C_1457,A_1458,B_1459)
      | ~ v1_funct_1(C_1457)
      | ~ m1_subset_1(C_1457,k1_zfmisc_1(k2_zfmisc_1(A_1458,B_1459))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_97157,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_97145])).

tff(c_97171,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_97157])).

tff(c_68,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_98046,plain,(
    ! [A_1505,B_1506,C_1507,D_1508] :
      ( r2_relset_1(A_1505,B_1506,C_1507,C_1507)
      | ~ m1_subset_1(D_1508,k1_zfmisc_1(k2_zfmisc_1(A_1505,B_1506)))
      | ~ m1_subset_1(C_1507,k1_zfmisc_1(k2_zfmisc_1(A_1505,B_1506))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_98126,plain,(
    ! [A_1512,C_1513] :
      ( r2_relset_1(A_1512,A_1512,C_1513,C_1513)
      | ~ m1_subset_1(C_1513,k1_zfmisc_1(k2_zfmisc_1(A_1512,A_1512))) ) ),
    inference(resolution,[status(thm)],[c_68,c_98046])).

tff(c_98140,plain,(
    ! [A_38] : r2_relset_1(A_38,A_38,k6_partfun1(A_38),k6_partfun1(A_38)) ),
    inference(resolution,[status(thm)],[c_68,c_98126])).

tff(c_96431,plain,(
    ! [C_1384,B_1385,A_1386] :
      ( v5_relat_1(C_1384,B_1385)
      | ~ m1_subset_1(C_1384,k1_zfmisc_1(k2_zfmisc_1(A_1386,B_1385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_96445,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_96431])).

tff(c_96629,plain,(
    ! [B_1413,A_1414] :
      ( k2_relat_1(B_1413) = A_1414
      | ~ v2_funct_2(B_1413,A_1414)
      | ~ v5_relat_1(B_1413,A_1414)
      | ~ v1_relat_1(B_1413) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_96638,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_96445,c_96629])).

tff(c_96647,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96395,c_96638])).

tff(c_96648,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_96647])).

tff(c_96989,plain,(
    ! [C_1446,B_1447,A_1448] :
      ( v2_funct_2(C_1446,B_1447)
      | ~ v3_funct_2(C_1446,A_1448,B_1447)
      | ~ v1_funct_1(C_1446)
      | ~ m1_subset_1(C_1446,k1_zfmisc_1(k2_zfmisc_1(A_1448,B_1447))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_97001,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_96989])).

tff(c_97013,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_97001])).

tff(c_97015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96648,c_97013])).

tff(c_97016,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_96647])).

tff(c_74,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_18,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_relat_1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_93,plain,(
    ! [A_9] :
      ( k5_relat_1(k2_funct_1(A_9),A_9) = k6_partfun1(k2_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18])).

tff(c_88,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_98290,plain,(
    ! [A_1524,B_1525] :
      ( k2_funct_2(A_1524,B_1525) = k2_funct_1(B_1525)
      | ~ m1_subset_1(B_1525,k1_zfmisc_1(k2_zfmisc_1(A_1524,A_1524)))
      | ~ v3_funct_2(B_1525,A_1524,A_1524)
      | ~ v1_funct_2(B_1525,A_1524,A_1524)
      | ~ v1_funct_1(B_1525) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_98299,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_98290])).

tff(c_98314,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_98299])).

tff(c_98232,plain,(
    ! [A_1520,B_1521] :
      ( v1_funct_1(k2_funct_2(A_1520,B_1521))
      | ~ m1_subset_1(B_1521,k1_zfmisc_1(k2_zfmisc_1(A_1520,A_1520)))
      | ~ v3_funct_2(B_1521,A_1520,A_1520)
      | ~ v1_funct_2(B_1521,A_1520,A_1520)
      | ~ v1_funct_1(B_1521) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_98241,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_98232])).

tff(c_98254,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_98241])).

tff(c_98315,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98314,c_98254])).

tff(c_58,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k2_funct_2(A_36,B_37),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k2_zfmisc_1(A_36,A_36)))
      | ~ v3_funct_2(B_37,A_36,A_36)
      | ~ v1_funct_2(B_37,A_36,A_36)
      | ~ v1_funct_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_100839,plain,(
    ! [D_1567,E_1569,B_1565,C_1566,A_1564,F_1568] :
      ( k1_partfun1(A_1564,B_1565,C_1566,D_1567,E_1569,F_1568) = k5_relat_1(E_1569,F_1568)
      | ~ m1_subset_1(F_1568,k1_zfmisc_1(k2_zfmisc_1(C_1566,D_1567)))
      | ~ v1_funct_1(F_1568)
      | ~ m1_subset_1(E_1569,k1_zfmisc_1(k2_zfmisc_1(A_1564,B_1565)))
      | ~ v1_funct_1(E_1569) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_100851,plain,(
    ! [A_1564,B_1565,E_1569] :
      ( k1_partfun1(A_1564,B_1565,'#skF_1','#skF_1',E_1569,'#skF_2') = k5_relat_1(E_1569,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_1569,k1_zfmisc_1(k2_zfmisc_1(A_1564,B_1565)))
      | ~ v1_funct_1(E_1569) ) ),
    inference(resolution,[status(thm)],[c_84,c_100839])).

tff(c_100878,plain,(
    ! [A_1570,B_1571,E_1572] :
      ( k1_partfun1(A_1570,B_1571,'#skF_1','#skF_1',E_1572,'#skF_2') = k5_relat_1(E_1572,'#skF_2')
      | ~ m1_subset_1(E_1572,k1_zfmisc_1(k2_zfmisc_1(A_1570,B_1571)))
      | ~ v1_funct_1(E_1572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_100851])).

tff(c_101638,plain,(
    ! [A_1587,B_1588] :
      ( k1_partfun1(A_1587,A_1587,'#skF_1','#skF_1',k2_funct_2(A_1587,B_1588),'#skF_2') = k5_relat_1(k2_funct_2(A_1587,B_1588),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_1587,B_1588))
      | ~ m1_subset_1(B_1588,k1_zfmisc_1(k2_zfmisc_1(A_1587,A_1587)))
      | ~ v3_funct_2(B_1588,A_1587,A_1587)
      | ~ v1_funct_2(B_1588,A_1587,A_1587)
      | ~ v1_funct_1(B_1588) ) ),
    inference(resolution,[status(thm)],[c_58,c_100878])).

tff(c_101654,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_101638])).

tff(c_101678,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_98315,c_98314,c_98314,c_98314,c_101654])).

tff(c_31488,plain,(
    ! [C_577,B_578,A_579] :
      ( v1_xboole_0(C_577)
      | ~ m1_subset_1(C_577,k1_zfmisc_1(k2_zfmisc_1(B_578,A_579)))
      | ~ v1_xboole_0(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_31502,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_31488])).

tff(c_31505,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_31502])).

tff(c_223,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_235,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_223])).

tff(c_1013,plain,(
    ! [C_154,A_155,B_156] :
      ( v2_funct_1(C_154)
      | ~ v3_funct_2(C_154,A_155,B_156)
      | ~ v1_funct_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1025,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_1013])).

tff(c_1039,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_1025])).

tff(c_1690,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( r2_relset_1(A_190,B_191,C_192,C_192)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1879,plain,(
    ! [A_204,C_205] :
      ( r2_relset_1(A_204,A_204,C_205,C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_204,A_204))) ) ),
    inference(resolution,[status(thm)],[c_68,c_1690])).

tff(c_1893,plain,(
    ! [A_38] : r2_relset_1(A_38,A_38,k6_partfun1(A_38),k6_partfun1(A_38)) ),
    inference(resolution,[status(thm)],[c_68,c_1879])).

tff(c_272,plain,(
    ! [C_69,B_70,A_71] :
      ( v5_relat_1(C_69,B_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_286,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_272])).

tff(c_474,plain,(
    ! [B_95,A_96] :
      ( k2_relat_1(B_95) = A_96
      | ~ v2_funct_2(B_95,A_96)
      | ~ v5_relat_1(B_95,A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_483,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_474])).

tff(c_492,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_483])).

tff(c_493,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_492])).

tff(c_747,plain,(
    ! [C_130,B_131,A_132] :
      ( v2_funct_2(C_130,B_131)
      | ~ v3_funct_2(C_130,A_132,B_131)
      | ~ v1_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_756,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_747])).

tff(c_767,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_756])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_767])).

tff(c_770,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_492])).

tff(c_14,plain,(
    ! [A_8] :
      ( k1_relat_1(A_8) = k1_xboole_0
      | k2_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_242,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_235,c_14])).

tff(c_291,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_772,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_291])).

tff(c_808,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_822,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_808])).

tff(c_1304,plain,(
    ! [B_178,A_179,C_180] :
      ( k1_xboole_0 = B_178
      | k1_relset_1(A_179,B_178,C_180) = A_179
      | ~ v1_funct_2(C_180,A_179,B_178)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_179,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1319,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_1304])).

tff(c_1336,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_822,c_1319])).

tff(c_1337,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_772,c_1336])).

tff(c_20,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k2_funct_1(A_9)) = k6_relat_1(k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,(
    ! [A_9] :
      ( k5_relat_1(A_9,k2_funct_1(A_9)) = k6_partfun1(k1_relat_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_20])).

tff(c_1953,plain,(
    ! [A_210,B_211] :
      ( k2_funct_2(A_210,B_211) = k2_funct_1(B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(k2_zfmisc_1(A_210,A_210)))
      | ~ v3_funct_2(B_211,A_210,A_210)
      | ~ v1_funct_2(B_211,A_210,A_210)
      | ~ v1_funct_1(B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1962,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_1953])).

tff(c_1977,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1962])).

tff(c_2594,plain,(
    ! [A_226,B_227] :
      ( m1_subset_1(k2_funct_2(A_226,B_227),k1_zfmisc_1(k2_zfmisc_1(A_226,A_226)))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(k2_zfmisc_1(A_226,A_226)))
      | ~ v3_funct_2(B_227,A_226,A_226)
      | ~ v1_funct_2(B_227,A_226,A_226)
      | ~ v1_funct_1(B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2641,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1977,c_2594])).

tff(c_2667,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_84,c_2641])).

tff(c_24,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2745,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2667,c_24])).

tff(c_1924,plain,(
    ! [A_207,B_208] :
      ( v1_funct_1(k2_funct_2(A_207,B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(A_207,A_207)))
      | ~ v3_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1933,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_1924])).

tff(c_1946,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1933])).

tff(c_1978,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_1946])).

tff(c_2044,plain,(
    ! [A_214,B_215] :
      ( v3_funct_2(k2_funct_2(A_214,B_215),A_214,A_214)
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_zfmisc_1(A_214,A_214)))
      | ~ v3_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2050,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_2044])).

tff(c_2061,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1977,c_2050])).

tff(c_36,plain,(
    ! [C_30,B_29,A_28] :
      ( v2_funct_2(C_30,B_29)
      | ~ v3_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2692,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2667,c_36])).

tff(c_2737,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_2061,c_2692])).

tff(c_26,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2744,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2667,c_26])).

tff(c_56,plain,(
    ! [B_35,A_34] :
      ( k2_relat_1(B_35) = A_34
      | ~ v2_funct_2(B_35,A_34)
      | ~ v5_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2757,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2744,c_56])).

tff(c_2760,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_2737,c_2757])).

tff(c_2254,plain,(
    ! [A_222,B_223] :
      ( v1_funct_2(k2_funct_2(A_222,B_223),A_222,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(k2_zfmisc_1(A_222,A_222)))
      | ~ v3_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_2(B_223,A_222,A_222)
      | ~ v1_funct_1(B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2260,plain,
    ( v1_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_2254])).

tff(c_2271,plain,(
    v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_1977,c_2260])).

tff(c_52,plain,(
    ! [B_32,A_31,C_33] :
      ( k1_xboole_0 = B_32
      | k1_relset_1(A_31,B_32,C_33) = A_31
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2689,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2667,c_52])).

tff(c_2733,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2271,c_2689])).

tff(c_2734,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_772,c_2733])).

tff(c_32,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2741,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_2')) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2667,c_32])).

tff(c_2940,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_2741])).

tff(c_76,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_48),k2_relat_1(A_48))))
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2761,plain,(
    ! [A_228,D_231,C_230,F_232,E_233,B_229] :
      ( k1_partfun1(A_228,B_229,C_230,D_231,E_233,F_232) = k5_relat_1(E_233,F_232)
      | ~ m1_subset_1(F_232,k1_zfmisc_1(k2_zfmisc_1(C_230,D_231)))
      | ~ v1_funct_1(F_232)
      | ~ m1_subset_1(E_233,k1_zfmisc_1(k2_zfmisc_1(A_228,B_229)))
      | ~ v1_funct_1(E_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_28620,plain,(
    ! [A_462,B_463,A_464,E_465] :
      ( k1_partfun1(A_462,B_463,k1_relat_1(A_464),k2_relat_1(A_464),E_465,A_464) = k5_relat_1(E_465,A_464)
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(A_462,B_463)))
      | ~ v1_funct_1(E_465)
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(resolution,[status(thm)],[c_76,c_2761])).

tff(c_28644,plain,(
    ! [A_464] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_464),k2_relat_1(A_464),'#skF_2',A_464) = k5_relat_1('#skF_2',A_464)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_funct_1(A_464)
      | ~ v1_relat_1(A_464) ) ),
    inference(resolution,[status(thm)],[c_84,c_28620])).

tff(c_29035,plain,(
    ! [A_469] :
      ( k1_partfun1('#skF_1','#skF_1',k1_relat_1(A_469),k2_relat_1(A_469),'#skF_2',A_469) = k5_relat_1('#skF_2',A_469)
      | ~ v1_funct_1(A_469)
      | ~ v1_relat_1(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_28644])).

tff(c_29065,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1',k2_relat_1(k2_funct_1('#skF_2')),'#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2940,c_29035])).

tff(c_29095,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_1978,c_2760,c_29065])).

tff(c_82,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_187,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_1979,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_187])).

tff(c_30188,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29095,c_1979])).

tff(c_30195,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_30188])).

tff(c_30198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_90,c_1039,c_1893,c_1337,c_30195])).

tff(c_30200,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_31604,plain,(
    ! [B_585,A_586] :
      ( k2_relat_1(B_585) = A_586
      | ~ v2_funct_2(B_585,A_586)
      | ~ v5_relat_1(B_585,A_586)
      | ~ v1_relat_1(B_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_31616,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_31604])).

tff(c_31628,plain,
    ( k1_xboole_0 = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_30200,c_31616])).

tff(c_31629,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_31628])).

tff(c_32269,plain,(
    ! [C_631,B_632,A_633] :
      ( v2_funct_2(C_631,B_632)
      | ~ v3_funct_2(C_631,A_633,B_632)
      | ~ v1_funct_1(C_631)
      | ~ m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(A_633,B_632))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_32284,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_32269])).

tff(c_32289,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_32284])).

tff(c_32291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31629,c_32289])).

tff(c_32292,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31628])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32322,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32292,c_2])).

tff(c_32326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31505,c_32322])).

tff(c_32328,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_31502])).

tff(c_139,plain,(
    ! [B_54,A_55] :
      ( ~ v1_xboole_0(B_54)
      | B_54 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_142,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_2,c_139])).

tff(c_32341,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32328,c_142])).

tff(c_32327,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_31502])).

tff(c_32334,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32327,c_142])).

tff(c_32374,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32341,c_32334])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32366,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32334,c_32334,c_10])).

tff(c_32527,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32374,c_32374,c_32366])).

tff(c_172,plain,(
    ! [B_62,A_63] :
      ( v1_xboole_0(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_172])).

tff(c_263,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_32528,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32527,c_263])).

tff(c_32531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32328,c_32528])).

tff(c_32533,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_32532,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_32539,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32532,c_142])).

tff(c_32598,plain,(
    ! [A_645] :
      ( A_645 = '#skF_2'
      | ~ v1_xboole_0(A_645) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_142])).

tff(c_32605,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32533,c_32598])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34025,plain,(
    ! [B_746,A_747] :
      ( B_746 = '#skF_2'
      | A_747 = '#skF_2'
      | k2_zfmisc_1(A_747,B_746) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_32539,c_32539,c_6])).

tff(c_34035,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_32605,c_34025])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_149,plain,(
    ! [A_57] : m1_subset_1(k6_partfun1(A_57),k1_zfmisc_1(k2_zfmisc_1(A_57,A_57))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_153,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_149])).

tff(c_175,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_153,c_172])).

tff(c_184,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_175])).

tff(c_193,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_184,c_142])).

tff(c_32545,plain,(
    k6_partfun1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_32539,c_193])).

tff(c_32625,plain,(
    ! [C_647,B_648,A_649] :
      ( v5_relat_1(C_647,B_648)
      | ~ m1_subset_1(C_647,k1_zfmisc_1(k2_zfmisc_1(A_649,B_648))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_32637,plain,(
    ! [A_650] : v5_relat_1(k6_partfun1(A_650),A_650) ),
    inference(resolution,[status(thm)],[c_68,c_32625])).

tff(c_32640,plain,(
    v5_relat_1('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32545,c_32637])).

tff(c_33108,plain,(
    ! [B_689,A_690] :
      ( B_689 = '#skF_2'
      | A_690 = '#skF_2'
      | k2_zfmisc_1(A_690,B_689) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_32539,c_32539,c_6])).

tff(c_33118,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_32605,c_33108])).

tff(c_16,plain,(
    ! [A_8] :
      ( k2_relat_1(A_8) = k1_xboole_0
      | k1_relat_1(A_8) != k1_xboole_0
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_243,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_235,c_16])).

tff(c_32641,plain,
    ( k2_relat_1('#skF_2') = '#skF_2'
    | k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_32539,c_243])).

tff(c_32642,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32641])).

tff(c_33152,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33118,c_33118,c_32642])).

tff(c_196,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_153])).

tff(c_32542,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_32539,c_196])).

tff(c_33149,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33118,c_33118,c_32542])).

tff(c_33162,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33118,c_88])).

tff(c_33158,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33118,c_32539])).

tff(c_50,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_94,plain,(
    ! [B_32,C_33] :
      ( k1_relset_1(k1_xboole_0,B_32,C_33) = k1_xboole_0
      | ~ v1_funct_2(C_33,k1_xboole_0,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_50])).

tff(c_33304,plain,(
    ! [B_697,C_698] :
      ( k1_relset_1('#skF_1',B_697,C_698) = '#skF_1'
      | ~ v1_funct_2(C_698,'#skF_1',B_697)
      | ~ m1_subset_1(C_698,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33158,c_33158,c_33158,c_33158,c_94])).

tff(c_33307,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_33162,c_33304])).

tff(c_33367,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33149,c_33307])).

tff(c_33060,plain,(
    ! [A_684,B_685,C_686] :
      ( k1_relset_1(A_684,B_685,C_686) = k1_relat_1(C_686)
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1(A_684,B_685))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_33074,plain,(
    ! [A_687] : k1_relset_1(A_687,A_687,k6_partfun1(A_687)) = k1_relat_1(k6_partfun1(A_687)) ),
    inference(resolution,[status(thm)],[c_68,c_33060])).

tff(c_33089,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relset_1('#skF_2','#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32545,c_33074])).

tff(c_33093,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_2') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32545,c_33089])).

tff(c_33126,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33118,c_33118,c_33118,c_33118,c_33093])).

tff(c_33416,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33367,c_33126])).

tff(c_33417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33152,c_33416])).

tff(c_33418,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32641])).

tff(c_33498,plain,(
    ! [B_707] :
      ( v2_funct_2(B_707,k2_relat_1(B_707))
      | ~ v5_relat_1(B_707,k2_relat_1(B_707))
      | ~ v1_relat_1(B_707) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_33501,plain,
    ( v2_funct_2('#skF_2',k2_relat_1('#skF_2'))
    | ~ v5_relat_1('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_33418,c_33498])).

tff(c_33503,plain,(
    v2_funct_2('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_32640,c_33418,c_33501])).

tff(c_34061,plain,(
    v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34035,c_34035,c_33503])).

tff(c_32636,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_32625])).

tff(c_33738,plain,(
    ! [B_724,A_725] :
      ( k2_relat_1(B_724) = A_725
      | ~ v2_funct_2(B_724,A_725)
      | ~ v5_relat_1(B_724,A_725)
      | ~ v1_relat_1(B_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_33750,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32636,c_33738])).

tff(c_33762,plain,
    ( '#skF_2' = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_33418,c_33750])).

tff(c_33763,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_33762])).

tff(c_34051,plain,(
    ~ v2_funct_2('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34035,c_33763])).

tff(c_34206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34061,c_34051])).

tff(c_34207,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_33762])).

tff(c_34236,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_34207,c_32545])).

tff(c_32550,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_32539,c_8])).

tff(c_34406,plain,(
    ! [A_760] : k2_zfmisc_1(A_760,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_34207,c_32550])).

tff(c_34433,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34406,c_68])).

tff(c_34445,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34236,c_34433])).

tff(c_34230,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_34207,c_32550])).

tff(c_35736,plain,(
    ! [A_866,B_867,C_868,D_869] :
      ( r2_relset_1(A_866,B_867,C_868,C_868)
      | ~ m1_subset_1(D_869,k1_zfmisc_1(k2_zfmisc_1(A_866,B_867)))
      | ~ m1_subset_1(C_868,k1_zfmisc_1(k2_zfmisc_1(A_866,B_867))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_35738,plain,(
    ! [A_3,C_868,D_869] :
      ( r2_relset_1(A_3,'#skF_1',C_868,C_868)
      | ~ m1_subset_1(D_869,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_868,k1_zfmisc_1(k2_zfmisc_1(A_3,'#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34230,c_35736])).

tff(c_35745,plain,(
    ! [A_3,C_868,D_869] :
      ( r2_relset_1(A_3,'#skF_1',C_868,C_868)
      | ~ m1_subset_1(D_869,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(C_868,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34230,c_35738])).

tff(c_49807,plain,(
    ! [D_869] : ~ m1_subset_1(D_869,k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_35745])).

tff(c_49840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49807,c_34445])).

tff(c_49842,plain,(
    ! [A_1067,C_1068] :
      ( r2_relset_1(A_1067,'#skF_1',C_1068,C_1068)
      | ~ m1_subset_1(C_1068,k1_zfmisc_1('#skF_1')) ) ),
    inference(splitRight,[status(thm)],[c_35745])).

tff(c_49851,plain,(
    ! [A_1067] : r2_relset_1(A_1067,'#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_34445,c_49842])).

tff(c_34242,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_90])).

tff(c_34238,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_32532])).

tff(c_34240,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_86])).

tff(c_34239,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_235])).

tff(c_34227,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_34207,c_33418])).

tff(c_22,plain,(
    ! [A_10] : k2_funct_1(k6_relat_1(A_10)) = k6_relat_1(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_91,plain,(
    ! [A_10] : k2_funct_1(k6_partfun1(A_10)) = k6_partfun1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_22])).

tff(c_204,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_91])).

tff(c_211,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_204])).

tff(c_32544,plain,(
    k2_funct_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_32539,c_211])).

tff(c_34234,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_34207,c_32544])).

tff(c_34533,plain,(
    ! [A_770] :
      ( k5_relat_1(k2_funct_1(A_770),A_770) = k6_partfun1(k2_relat_1(A_770))
      | ~ v2_funct_1(A_770)
      | ~ v1_funct_1(A_770)
      | ~ v1_relat_1(A_770) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18])).

tff(c_34542,plain,
    ( k6_partfun1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34234,c_34533])).

tff(c_34549,plain,
    ( k5_relat_1('#skF_1','#skF_1') = '#skF_1'
    | ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34239,c_34242,c_34236,c_34227,c_34542])).

tff(c_34635,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34549])).

tff(c_33585,plain,(
    ! [C_711,B_712,A_713] :
      ( v1_xboole_0(C_711)
      | ~ m1_subset_1(C_711,k1_zfmisc_1(k2_zfmisc_1(B_712,A_713)))
      | ~ v1_xboole_0(A_713) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_33600,plain,(
    ! [A_38] :
      ( v1_xboole_0(k6_partfun1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_68,c_33585])).

tff(c_33601,plain,(
    ! [A_714] :
      ( v1_xboole_0(k6_partfun1(A_714))
      | ~ v1_xboole_0(A_714) ) ),
    inference(resolution,[status(thm)],[c_68,c_33585])).

tff(c_32549,plain,(
    ! [A_55] :
      ( A_55 = '#skF_2'
      | ~ v1_xboole_0(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_142])).

tff(c_33618,plain,(
    ! [A_715] :
      ( k6_partfun1(A_715) = '#skF_2'
      | ~ v1_xboole_0(A_715) ) ),
    inference(resolution,[status(thm)],[c_33601,c_32549])).

tff(c_33625,plain,(
    ! [A_38] :
      ( k6_partfun1(k6_partfun1(A_38)) = '#skF_2'
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_33600,c_33618])).

tff(c_34552,plain,(
    ! [A_771] :
      ( k6_partfun1(k6_partfun1(A_771)) = '#skF_1'
      | ~ v1_xboole_0(A_771) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_33625])).

tff(c_35320,plain,(
    ! [A_836] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k6_partfun1(A_836),k6_partfun1(A_836))))
      | ~ v1_xboole_0(A_836) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34552,c_68])).

tff(c_38,plain,(
    ! [C_30,A_28,B_29] :
      ( v2_funct_1(C_30)
      | ~ v3_funct_2(C_30,A_28,B_29)
      | ~ v1_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_35342,plain,(
    ! [A_836] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',k6_partfun1(A_836),k6_partfun1(A_836))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_xboole_0(A_836) ) ),
    inference(resolution,[status(thm)],[c_35320,c_38])).

tff(c_35402,plain,(
    ! [A_836] :
      ( v2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',k6_partfun1(A_836),k6_partfun1(A_836))
      | ~ v1_xboole_0(A_836) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34242,c_35342])).

tff(c_35422,plain,(
    ! [A_837] :
      ( ~ v3_funct_2('#skF_1',k6_partfun1(A_837),k6_partfun1(A_837))
      | ~ v1_xboole_0(A_837) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34635,c_35402])).

tff(c_35443,plain,
    ( ~ v3_funct_2('#skF_1','#skF_1',k6_partfun1('#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34236,c_35422])).

tff(c_35449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34238,c_34240,c_34236,c_35443])).

tff(c_35450,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_34549])).

tff(c_33419,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32641])).

tff(c_34226,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_34207,c_33419])).

tff(c_37224,plain,(
    ! [C_932,E_935,F_934,B_931,D_933,A_930] :
      ( k1_partfun1(A_930,B_931,C_932,D_933,E_935,F_934) = k5_relat_1(E_935,F_934)
      | ~ m1_subset_1(F_934,k1_zfmisc_1(k2_zfmisc_1(C_932,D_933)))
      | ~ v1_funct_1(F_934)
      | ~ m1_subset_1(E_935,k1_zfmisc_1(k2_zfmisc_1(A_930,B_931)))
      | ~ v1_funct_1(E_935) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_55142,plain,(
    ! [A_1095,B_1096,A_1097,E_1098] :
      ( k1_partfun1(A_1095,B_1096,k1_relat_1(A_1097),k2_relat_1(A_1097),E_1098,A_1097) = k5_relat_1(E_1098,A_1097)
      | ~ m1_subset_1(E_1098,k1_zfmisc_1(k2_zfmisc_1(A_1095,B_1096)))
      | ~ v1_funct_1(E_1098)
      | ~ v1_funct_1(A_1097)
      | ~ v1_relat_1(A_1097) ) ),
    inference(resolution,[status(thm)],[c_76,c_37224])).

tff(c_75001,plain,(
    ! [A_1259,A_1260] :
      ( k1_partfun1(A_1259,A_1259,k1_relat_1(A_1260),k2_relat_1(A_1260),k6_partfun1(A_1259),A_1260) = k5_relat_1(k6_partfun1(A_1259),A_1260)
      | ~ v1_funct_1(k6_partfun1(A_1259))
      | ~ v1_funct_1(A_1260)
      | ~ v1_relat_1(A_1260) ) ),
    inference(resolution,[status(thm)],[c_68,c_55142])).

tff(c_75109,plain,(
    ! [A_1259] :
      ( k1_partfun1(A_1259,A_1259,'#skF_1',k2_relat_1('#skF_1'),k6_partfun1(A_1259),'#skF_1') = k5_relat_1(k6_partfun1(A_1259),'#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_1259))
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34226,c_75001])).

tff(c_96277,plain,(
    ! [A_1378] :
      ( k1_partfun1(A_1378,A_1378,'#skF_1','#skF_1',k6_partfun1(A_1378),'#skF_1') = k5_relat_1(k6_partfun1(A_1378),'#skF_1')
      | ~ v1_funct_1(k6_partfun1(A_1378)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34239,c_34242,c_34227,c_75109])).

tff(c_96325,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k6_partfun1('#skF_1'),'#skF_1') = k5_relat_1(k6_partfun1('#skF_1'),'#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34236,c_96277])).

tff(c_96339,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34242,c_35450,c_34236,c_34236,c_96325])).

tff(c_32551,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_2',B_4) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32539,c_32539,c_10])).

tff(c_34374,plain,(
    ! [B_759] : k2_zfmisc_1('#skF_1',B_759) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_34207,c_32551])).

tff(c_35888,plain,(
    ! [B_888,C_889] :
      ( k1_relset_1('#skF_1',B_888,C_889) = k1_relat_1(C_889)
      | ~ m1_subset_1(C_889,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34374,c_32])).

tff(c_35890,plain,(
    ! [B_888] : k1_relset_1('#skF_1',B_888,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_34445,c_35888])).

tff(c_35892,plain,(
    ! [B_888] : k1_relset_1('#skF_1',B_888,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34226,c_35890])).

tff(c_34237,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_32539])).

tff(c_46,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_95,plain,(
    ! [C_33,B_32] :
      ( v1_funct_2(C_33,k1_xboole_0,B_32)
      | k1_relset_1(k1_xboole_0,B_32,C_33) != k1_xboole_0
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_46])).

tff(c_34465,plain,(
    ! [C_762,B_763] :
      ( v1_funct_2(C_762,'#skF_1',B_763)
      | k1_relset_1('#skF_1',B_763,C_762) != '#skF_1'
      | ~ m1_subset_1(C_762,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34237,c_34237,c_34237,c_34237,c_95])).

tff(c_34468,plain,(
    ! [B_763] :
      ( v1_funct_2('#skF_1','#skF_1',B_763)
      | k1_relset_1('#skF_1',B_763,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_34445,c_34465])).

tff(c_35894,plain,(
    ! [B_763] : v1_funct_2('#skF_1','#skF_1',B_763) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35892,c_34468])).

tff(c_35910,plain,(
    ! [A_891,B_892] :
      ( k2_funct_2(A_891,B_892) = k2_funct_1(B_892)
      | ~ m1_subset_1(B_892,k1_zfmisc_1(k2_zfmisc_1(A_891,A_891)))
      | ~ v3_funct_2(B_892,A_891,A_891)
      | ~ v1_funct_2(B_892,A_891,A_891)
      | ~ v1_funct_1(B_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_35921,plain,(
    ! [A_38] :
      ( k2_funct_2(A_38,k6_partfun1(A_38)) = k2_funct_1(k6_partfun1(A_38))
      | ~ v3_funct_2(k6_partfun1(A_38),A_38,A_38)
      | ~ v1_funct_2(k6_partfun1(A_38),A_38,A_38)
      | ~ v1_funct_1(k6_partfun1(A_38)) ) ),
    inference(resolution,[status(thm)],[c_68,c_35910])).

tff(c_44481,plain,(
    ! [A_1016] :
      ( k2_funct_2(A_1016,k6_partfun1(A_1016)) = k6_partfun1(A_1016)
      | ~ v3_funct_2(k6_partfun1(A_1016),A_1016,A_1016)
      | ~ v1_funct_2(k6_partfun1(A_1016),A_1016,A_1016)
      | ~ v1_funct_1(k6_partfun1(A_1016)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_35921])).

tff(c_44514,plain,
    ( k2_funct_2('#skF_1',k6_partfun1('#skF_1')) = k6_partfun1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2(k6_partfun1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34236,c_44481])).

tff(c_44516,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34242,c_34236,c_35894,c_34236,c_34240,c_34236,c_34236,c_44514])).

tff(c_33488,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32605,c_68])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_33507,plain,
    ( v1_xboole_0(k6_partfun1('#skF_1'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_33488,c_12])).

tff(c_33510,plain,(
    v1_xboole_0(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32532,c_33507])).

tff(c_33517,plain,(
    k6_partfun1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_33510,c_32549])).

tff(c_33521,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33517,c_187])).

tff(c_34216,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34207,c_34207,c_34207,c_33521])).

tff(c_44518,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44516,c_34216])).

tff(c_96340,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96339,c_44518])).

tff(c_96343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49851,c_96340])).

tff(c_96344,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_98317,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98314,c_96344])).

tff(c_101698,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101678,c_98317])).

tff(c_101705,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_101698])).

tff(c_101708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96395,c_90,c_97171,c_98140,c_97016,c_101705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.88/13.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.88/13.24  
% 22.88/13.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.88/13.24  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 22.88/13.24  
% 22.88/13.24  %Foreground sorts:
% 22.88/13.24  
% 22.88/13.24  
% 22.88/13.24  %Background operators:
% 22.88/13.24  
% 22.88/13.24  
% 22.88/13.24  %Foreground operators:
% 22.88/13.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.88/13.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 22.88/13.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 22.88/13.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.88/13.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 22.88/13.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.88/13.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 22.88/13.24  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 22.88/13.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 22.88/13.24  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 22.88/13.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.88/13.24  tff('#skF_2', type, '#skF_2': $i).
% 22.88/13.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 22.88/13.24  tff('#skF_1', type, '#skF_1': $i).
% 22.88/13.24  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 22.88/13.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 22.88/13.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.88/13.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.88/13.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 22.88/13.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.88/13.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.88/13.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.88/13.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 22.88/13.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.88/13.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.88/13.24  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 22.88/13.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.88/13.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.88/13.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.88/13.24  
% 23.19/13.28  tff(f_195, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 23.19/13.28  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.19/13.28  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 23.19/13.28  tff(f_150, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 23.19/13.28  tff(f_92, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 23.19/13.28  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.19/13.28  tff(f_130, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 23.19/13.28  tff(f_172, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 23.19/13.28  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 23.19/13.28  tff(f_170, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 23.19/13.28  tff(f_146, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 23.19/13.28  tff(f_160, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 23.19/13.28  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 23.19/13.28  tff(f_53, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 23.19/13.28  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 23.19/13.28  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 23.19/13.28  tff(f_182, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 23.19/13.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 23.19/13.28  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 23.19/13.28  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 23.19/13.28  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 23.19/13.28  tff(f_65, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 23.19/13.28  tff(c_84, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 23.19/13.28  tff(c_96383, plain, (![C_1379, A_1380, B_1381]: (v1_relat_1(C_1379) | ~m1_subset_1(C_1379, k1_zfmisc_1(k2_zfmisc_1(A_1380, B_1381))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 23.19/13.28  tff(c_96395, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_96383])).
% 23.19/13.28  tff(c_90, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 23.19/13.28  tff(c_86, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 23.19/13.28  tff(c_97145, plain, (![C_1457, A_1458, B_1459]: (v2_funct_1(C_1457) | ~v3_funct_2(C_1457, A_1458, B_1459) | ~v1_funct_1(C_1457) | ~m1_subset_1(C_1457, k1_zfmisc_1(k2_zfmisc_1(A_1458, B_1459))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 23.19/13.28  tff(c_97157, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_97145])).
% 23.19/13.28  tff(c_97171, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_97157])).
% 23.19/13.28  tff(c_68, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 23.19/13.28  tff(c_98046, plain, (![A_1505, B_1506, C_1507, D_1508]: (r2_relset_1(A_1505, B_1506, C_1507, C_1507) | ~m1_subset_1(D_1508, k1_zfmisc_1(k2_zfmisc_1(A_1505, B_1506))) | ~m1_subset_1(C_1507, k1_zfmisc_1(k2_zfmisc_1(A_1505, B_1506))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 23.19/13.28  tff(c_98126, plain, (![A_1512, C_1513]: (r2_relset_1(A_1512, A_1512, C_1513, C_1513) | ~m1_subset_1(C_1513, k1_zfmisc_1(k2_zfmisc_1(A_1512, A_1512))))), inference(resolution, [status(thm)], [c_68, c_98046])).
% 23.19/13.28  tff(c_98140, plain, (![A_38]: (r2_relset_1(A_38, A_38, k6_partfun1(A_38), k6_partfun1(A_38)))), inference(resolution, [status(thm)], [c_68, c_98126])).
% 23.19/13.28  tff(c_96431, plain, (![C_1384, B_1385, A_1386]: (v5_relat_1(C_1384, B_1385) | ~m1_subset_1(C_1384, k1_zfmisc_1(k2_zfmisc_1(A_1386, B_1385))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.19/13.28  tff(c_96445, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_96431])).
% 23.19/13.28  tff(c_96629, plain, (![B_1413, A_1414]: (k2_relat_1(B_1413)=A_1414 | ~v2_funct_2(B_1413, A_1414) | ~v5_relat_1(B_1413, A_1414) | ~v1_relat_1(B_1413))), inference(cnfTransformation, [status(thm)], [f_130])).
% 23.19/13.28  tff(c_96638, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_96445, c_96629])).
% 23.19/13.28  tff(c_96647, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96395, c_96638])).
% 23.19/13.28  tff(c_96648, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_96647])).
% 23.19/13.28  tff(c_96989, plain, (![C_1446, B_1447, A_1448]: (v2_funct_2(C_1446, B_1447) | ~v3_funct_2(C_1446, A_1448, B_1447) | ~v1_funct_1(C_1446) | ~m1_subset_1(C_1446, k1_zfmisc_1(k2_zfmisc_1(A_1448, B_1447))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 23.19/13.28  tff(c_97001, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_96989])).
% 23.19/13.28  tff(c_97013, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_97001])).
% 23.19/13.28  tff(c_97015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96648, c_97013])).
% 23.19/13.28  tff(c_97016, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_96647])).
% 23.19/13.28  tff(c_74, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_172])).
% 23.19/13.28  tff(c_18, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_relat_1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.19/13.28  tff(c_93, plain, (![A_9]: (k5_relat_1(k2_funct_1(A_9), A_9)=k6_partfun1(k2_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18])).
% 23.19/13.28  tff(c_88, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 23.19/13.28  tff(c_98290, plain, (![A_1524, B_1525]: (k2_funct_2(A_1524, B_1525)=k2_funct_1(B_1525) | ~m1_subset_1(B_1525, k1_zfmisc_1(k2_zfmisc_1(A_1524, A_1524))) | ~v3_funct_2(B_1525, A_1524, A_1524) | ~v1_funct_2(B_1525, A_1524, A_1524) | ~v1_funct_1(B_1525))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.19/13.28  tff(c_98299, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_98290])).
% 23.19/13.28  tff(c_98314, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_98299])).
% 23.19/13.28  tff(c_98232, plain, (![A_1520, B_1521]: (v1_funct_1(k2_funct_2(A_1520, B_1521)) | ~m1_subset_1(B_1521, k1_zfmisc_1(k2_zfmisc_1(A_1520, A_1520))) | ~v3_funct_2(B_1521, A_1520, A_1520) | ~v1_funct_2(B_1521, A_1520, A_1520) | ~v1_funct_1(B_1521))), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.19/13.28  tff(c_98241, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_98232])).
% 23.19/13.28  tff(c_98254, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_98241])).
% 23.19/13.28  tff(c_98315, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_98314, c_98254])).
% 23.19/13.28  tff(c_58, plain, (![A_36, B_37]: (m1_subset_1(k2_funct_2(A_36, B_37), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))) | ~v3_funct_2(B_37, A_36, A_36) | ~v1_funct_2(B_37, A_36, A_36) | ~v1_funct_1(B_37))), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.19/13.28  tff(c_100839, plain, (![D_1567, E_1569, B_1565, C_1566, A_1564, F_1568]: (k1_partfun1(A_1564, B_1565, C_1566, D_1567, E_1569, F_1568)=k5_relat_1(E_1569, F_1568) | ~m1_subset_1(F_1568, k1_zfmisc_1(k2_zfmisc_1(C_1566, D_1567))) | ~v1_funct_1(F_1568) | ~m1_subset_1(E_1569, k1_zfmisc_1(k2_zfmisc_1(A_1564, B_1565))) | ~v1_funct_1(E_1569))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.19/13.28  tff(c_100851, plain, (![A_1564, B_1565, E_1569]: (k1_partfun1(A_1564, B_1565, '#skF_1', '#skF_1', E_1569, '#skF_2')=k5_relat_1(E_1569, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_1569, k1_zfmisc_1(k2_zfmisc_1(A_1564, B_1565))) | ~v1_funct_1(E_1569))), inference(resolution, [status(thm)], [c_84, c_100839])).
% 23.19/13.28  tff(c_100878, plain, (![A_1570, B_1571, E_1572]: (k1_partfun1(A_1570, B_1571, '#skF_1', '#skF_1', E_1572, '#skF_2')=k5_relat_1(E_1572, '#skF_2') | ~m1_subset_1(E_1572, k1_zfmisc_1(k2_zfmisc_1(A_1570, B_1571))) | ~v1_funct_1(E_1572))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_100851])).
% 23.19/13.28  tff(c_101638, plain, (![A_1587, B_1588]: (k1_partfun1(A_1587, A_1587, '#skF_1', '#skF_1', k2_funct_2(A_1587, B_1588), '#skF_2')=k5_relat_1(k2_funct_2(A_1587, B_1588), '#skF_2') | ~v1_funct_1(k2_funct_2(A_1587, B_1588)) | ~m1_subset_1(B_1588, k1_zfmisc_1(k2_zfmisc_1(A_1587, A_1587))) | ~v3_funct_2(B_1588, A_1587, A_1587) | ~v1_funct_2(B_1588, A_1587, A_1587) | ~v1_funct_1(B_1588))), inference(resolution, [status(thm)], [c_58, c_100878])).
% 23.19/13.28  tff(c_101654, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_101638])).
% 23.19/13.28  tff(c_101678, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_98315, c_98314, c_98314, c_98314, c_101654])).
% 23.19/13.28  tff(c_31488, plain, (![C_577, B_578, A_579]: (v1_xboole_0(C_577) | ~m1_subset_1(C_577, k1_zfmisc_1(k2_zfmisc_1(B_578, A_579))) | ~v1_xboole_0(A_579))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.19/13.28  tff(c_31502, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_31488])).
% 23.19/13.28  tff(c_31505, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_31502])).
% 23.19/13.28  tff(c_223, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 23.19/13.28  tff(c_235, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_223])).
% 23.19/13.28  tff(c_1013, plain, (![C_154, A_155, B_156]: (v2_funct_1(C_154) | ~v3_funct_2(C_154, A_155, B_156) | ~v1_funct_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 23.19/13.28  tff(c_1025, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_1013])).
% 23.19/13.28  tff(c_1039, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_1025])).
% 23.19/13.28  tff(c_1690, plain, (![A_190, B_191, C_192, D_193]: (r2_relset_1(A_190, B_191, C_192, C_192) | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 23.19/13.28  tff(c_1879, plain, (![A_204, C_205]: (r2_relset_1(A_204, A_204, C_205, C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_204, A_204))))), inference(resolution, [status(thm)], [c_68, c_1690])).
% 23.19/13.28  tff(c_1893, plain, (![A_38]: (r2_relset_1(A_38, A_38, k6_partfun1(A_38), k6_partfun1(A_38)))), inference(resolution, [status(thm)], [c_68, c_1879])).
% 23.19/13.28  tff(c_272, plain, (![C_69, B_70, A_71]: (v5_relat_1(C_69, B_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.19/13.28  tff(c_286, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_272])).
% 23.19/13.28  tff(c_474, plain, (![B_95, A_96]: (k2_relat_1(B_95)=A_96 | ~v2_funct_2(B_95, A_96) | ~v5_relat_1(B_95, A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_130])).
% 23.19/13.28  tff(c_483, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_286, c_474])).
% 23.19/13.28  tff(c_492, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_483])).
% 23.19/13.28  tff(c_493, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_492])).
% 23.19/13.28  tff(c_747, plain, (![C_130, B_131, A_132]: (v2_funct_2(C_130, B_131) | ~v3_funct_2(C_130, A_132, B_131) | ~v1_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 23.19/13.28  tff(c_756, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_747])).
% 23.19/13.28  tff(c_767, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_756])).
% 23.19/13.28  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_767])).
% 23.19/13.28  tff(c_770, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_492])).
% 23.19/13.28  tff(c_14, plain, (![A_8]: (k1_relat_1(A_8)=k1_xboole_0 | k2_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.19/13.28  tff(c_242, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_235, c_14])).
% 23.19/13.28  tff(c_291, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_242])).
% 23.19/13.28  tff(c_772, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_770, c_291])).
% 23.19/13.28  tff(c_808, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.19/13.28  tff(c_822, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_808])).
% 23.19/13.28  tff(c_1304, plain, (![B_178, A_179, C_180]: (k1_xboole_0=B_178 | k1_relset_1(A_179, B_178, C_180)=A_179 | ~v1_funct_2(C_180, A_179, B_178) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_179, B_178))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.19/13.28  tff(c_1319, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_1304])).
% 23.19/13.28  tff(c_1336, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_822, c_1319])).
% 23.19/13.28  tff(c_1337, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_772, c_1336])).
% 23.19/13.28  tff(c_20, plain, (![A_9]: (k5_relat_1(A_9, k2_funct_1(A_9))=k6_relat_1(k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.19/13.28  tff(c_92, plain, (![A_9]: (k5_relat_1(A_9, k2_funct_1(A_9))=k6_partfun1(k1_relat_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_20])).
% 23.19/13.28  tff(c_1953, plain, (![A_210, B_211]: (k2_funct_2(A_210, B_211)=k2_funct_1(B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(k2_zfmisc_1(A_210, A_210))) | ~v3_funct_2(B_211, A_210, A_210) | ~v1_funct_2(B_211, A_210, A_210) | ~v1_funct_1(B_211))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.19/13.28  tff(c_1962, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_1953])).
% 23.19/13.28  tff(c_1977, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1962])).
% 23.19/13.28  tff(c_2594, plain, (![A_226, B_227]: (m1_subset_1(k2_funct_2(A_226, B_227), k1_zfmisc_1(k2_zfmisc_1(A_226, A_226))) | ~m1_subset_1(B_227, k1_zfmisc_1(k2_zfmisc_1(A_226, A_226))) | ~v3_funct_2(B_227, A_226, A_226) | ~v1_funct_2(B_227, A_226, A_226) | ~v1_funct_1(B_227))), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.19/13.28  tff(c_2641, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1977, c_2594])).
% 23.19/13.28  tff(c_2667, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_84, c_2641])).
% 23.19/13.28  tff(c_24, plain, (![C_13, A_11, B_12]: (v1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 23.19/13.28  tff(c_2745, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2667, c_24])).
% 23.19/13.28  tff(c_1924, plain, (![A_207, B_208]: (v1_funct_1(k2_funct_2(A_207, B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_zfmisc_1(A_207, A_207))) | ~v3_funct_2(B_208, A_207, A_207) | ~v1_funct_2(B_208, A_207, A_207) | ~v1_funct_1(B_208))), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.19/13.28  tff(c_1933, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_1924])).
% 23.19/13.28  tff(c_1946, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1933])).
% 23.19/13.28  tff(c_1978, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1977, c_1946])).
% 23.19/13.28  tff(c_2044, plain, (![A_214, B_215]: (v3_funct_2(k2_funct_2(A_214, B_215), A_214, A_214) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_zfmisc_1(A_214, A_214))) | ~v3_funct_2(B_215, A_214, A_214) | ~v1_funct_2(B_215, A_214, A_214) | ~v1_funct_1(B_215))), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.19/13.28  tff(c_2050, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_2044])).
% 23.19/13.28  tff(c_2061, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1977, c_2050])).
% 23.19/13.28  tff(c_36, plain, (![C_30, B_29, A_28]: (v2_funct_2(C_30, B_29) | ~v3_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 23.19/13.28  tff(c_2692, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2667, c_36])).
% 23.19/13.28  tff(c_2737, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_2061, c_2692])).
% 23.19/13.28  tff(c_26, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.19/13.28  tff(c_2744, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_2667, c_26])).
% 23.19/13.28  tff(c_56, plain, (![B_35, A_34]: (k2_relat_1(B_35)=A_34 | ~v2_funct_2(B_35, A_34) | ~v5_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_130])).
% 23.19/13.28  tff(c_2757, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2744, c_56])).
% 23.19/13.28  tff(c_2760, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_2737, c_2757])).
% 23.19/13.28  tff(c_2254, plain, (![A_222, B_223]: (v1_funct_2(k2_funct_2(A_222, B_223), A_222, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(k2_zfmisc_1(A_222, A_222))) | ~v3_funct_2(B_223, A_222, A_222) | ~v1_funct_2(B_223, A_222, A_222) | ~v1_funct_1(B_223))), inference(cnfTransformation, [status(thm)], [f_146])).
% 23.19/13.28  tff(c_2260, plain, (v1_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_2254])).
% 23.19/13.28  tff(c_2271, plain, (v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_1977, c_2260])).
% 23.19/13.28  tff(c_52, plain, (![B_32, A_31, C_33]: (k1_xboole_0=B_32 | k1_relset_1(A_31, B_32, C_33)=A_31 | ~v1_funct_2(C_33, A_31, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.19/13.28  tff(c_2689, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2667, c_52])).
% 23.19/13.28  tff(c_2733, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2271, c_2689])).
% 23.19/13.28  tff(c_2734, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_772, c_2733])).
% 23.19/13.28  tff(c_32, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.19/13.28  tff(c_2741, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_2'))=k1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_2667, c_32])).
% 23.19/13.28  tff(c_2940, plain, (k1_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_2741])).
% 23.19/13.28  tff(c_76, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_48), k2_relat_1(A_48)))) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_182])).
% 23.19/13.28  tff(c_2761, plain, (![A_228, D_231, C_230, F_232, E_233, B_229]: (k1_partfun1(A_228, B_229, C_230, D_231, E_233, F_232)=k5_relat_1(E_233, F_232) | ~m1_subset_1(F_232, k1_zfmisc_1(k2_zfmisc_1(C_230, D_231))) | ~v1_funct_1(F_232) | ~m1_subset_1(E_233, k1_zfmisc_1(k2_zfmisc_1(A_228, B_229))) | ~v1_funct_1(E_233))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.19/13.28  tff(c_28620, plain, (![A_462, B_463, A_464, E_465]: (k1_partfun1(A_462, B_463, k1_relat_1(A_464), k2_relat_1(A_464), E_465, A_464)=k5_relat_1(E_465, A_464) | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(A_462, B_463))) | ~v1_funct_1(E_465) | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(resolution, [status(thm)], [c_76, c_2761])).
% 23.19/13.28  tff(c_28644, plain, (![A_464]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_464), k2_relat_1(A_464), '#skF_2', A_464)=k5_relat_1('#skF_2', A_464) | ~v1_funct_1('#skF_2') | ~v1_funct_1(A_464) | ~v1_relat_1(A_464))), inference(resolution, [status(thm)], [c_84, c_28620])).
% 23.19/13.28  tff(c_29035, plain, (![A_469]: (k1_partfun1('#skF_1', '#skF_1', k1_relat_1(A_469), k2_relat_1(A_469), '#skF_2', A_469)=k5_relat_1('#skF_2', A_469) | ~v1_funct_1(A_469) | ~v1_relat_1(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_28644])).
% 23.19/13.28  tff(c_29065, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', k2_relat_1(k2_funct_1('#skF_2')), '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2940, c_29035])).
% 23.19/13.28  tff(c_29095, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_1978, c_2760, c_29065])).
% 23.19/13.28  tff(c_82, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 23.19/13.28  tff(c_187, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_82])).
% 23.19/13.28  tff(c_1979, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1977, c_187])).
% 23.19/13.28  tff(c_30188, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_29095, c_1979])).
% 23.19/13.28  tff(c_30195, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_92, c_30188])).
% 23.19/13.28  tff(c_30198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_235, c_90, c_1039, c_1893, c_1337, c_30195])).
% 23.19/13.28  tff(c_30200, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_242])).
% 23.19/13.28  tff(c_31604, plain, (![B_585, A_586]: (k2_relat_1(B_585)=A_586 | ~v2_funct_2(B_585, A_586) | ~v5_relat_1(B_585, A_586) | ~v1_relat_1(B_585))), inference(cnfTransformation, [status(thm)], [f_130])).
% 23.19/13.28  tff(c_31616, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_286, c_31604])).
% 23.19/13.28  tff(c_31628, plain, (k1_xboole_0='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_30200, c_31616])).
% 23.19/13.28  tff(c_31629, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_31628])).
% 23.19/13.28  tff(c_32269, plain, (![C_631, B_632, A_633]: (v2_funct_2(C_631, B_632) | ~v3_funct_2(C_631, A_633, B_632) | ~v1_funct_1(C_631) | ~m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(A_633, B_632))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 23.19/13.28  tff(c_32284, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_84, c_32269])).
% 23.19/13.28  tff(c_32289, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_32284])).
% 23.19/13.28  tff(c_32291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31629, c_32289])).
% 23.19/13.28  tff(c_32292, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_31628])).
% 23.19/13.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 23.19/13.28  tff(c_32322, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32292, c_2])).
% 23.19/13.28  tff(c_32326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31505, c_32322])).
% 23.19/13.28  tff(c_32328, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_31502])).
% 23.19/13.28  tff(c_139, plain, (![B_54, A_55]: (~v1_xboole_0(B_54) | B_54=A_55 | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 23.19/13.28  tff(c_142, plain, (![A_55]: (k1_xboole_0=A_55 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_2, c_139])).
% 23.19/13.28  tff(c_32341, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_32328, c_142])).
% 23.19/13.28  tff(c_32327, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_31502])).
% 23.19/13.28  tff(c_32334, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32327, c_142])).
% 23.19/13.28  tff(c_32374, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32341, c_32334])).
% 23.19/13.28  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.19/13.28  tff(c_32366, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32334, c_32334, c_10])).
% 23.19/13.28  tff(c_32527, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32374, c_32374, c_32366])).
% 23.19/13.28  tff(c_172, plain, (![B_62, A_63]: (v1_xboole_0(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.19/13.28  tff(c_186, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_84, c_172])).
% 23.19/13.28  tff(c_263, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitLeft, [status(thm)], [c_186])).
% 23.19/13.28  tff(c_32528, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32527, c_263])).
% 23.19/13.28  tff(c_32531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32328, c_32528])).
% 23.19/13.28  tff(c_32533, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(splitRight, [status(thm)], [c_186])).
% 23.19/13.28  tff(c_32532, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_186])).
% 23.19/13.28  tff(c_32539, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32532, c_142])).
% 23.19/13.28  tff(c_32598, plain, (![A_645]: (A_645='#skF_2' | ~v1_xboole_0(A_645))), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_142])).
% 23.19/13.28  tff(c_32605, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_32533, c_32598])).
% 23.19/13.28  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.19/13.28  tff(c_34025, plain, (![B_746, A_747]: (B_746='#skF_2' | A_747='#skF_2' | k2_zfmisc_1(A_747, B_746)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_32539, c_32539, c_6])).
% 23.19/13.28  tff(c_34035, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_32605, c_34025])).
% 23.19/13.28  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.19/13.28  tff(c_149, plain, (![A_57]: (m1_subset_1(k6_partfun1(A_57), k1_zfmisc_1(k2_zfmisc_1(A_57, A_57))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 23.19/13.28  tff(c_153, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_149])).
% 23.19/13.28  tff(c_175, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_172])).
% 23.19/13.28  tff(c_184, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_175])).
% 23.19/13.28  tff(c_193, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_184, c_142])).
% 23.19/13.28  tff(c_32545, plain, (k6_partfun1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_32539, c_193])).
% 23.19/13.28  tff(c_32625, plain, (![C_647, B_648, A_649]: (v5_relat_1(C_647, B_648) | ~m1_subset_1(C_647, k1_zfmisc_1(k2_zfmisc_1(A_649, B_648))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.19/13.28  tff(c_32637, plain, (![A_650]: (v5_relat_1(k6_partfun1(A_650), A_650))), inference(resolution, [status(thm)], [c_68, c_32625])).
% 23.19/13.28  tff(c_32640, plain, (v5_relat_1('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32545, c_32637])).
% 23.19/13.28  tff(c_33108, plain, (![B_689, A_690]: (B_689='#skF_2' | A_690='#skF_2' | k2_zfmisc_1(A_690, B_689)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_32539, c_32539, c_6])).
% 23.19/13.28  tff(c_33118, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_32605, c_33108])).
% 23.19/13.28  tff(c_16, plain, (![A_8]: (k2_relat_1(A_8)=k1_xboole_0 | k1_relat_1(A_8)!=k1_xboole_0 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.19/13.28  tff(c_243, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_235, c_16])).
% 23.19/13.28  tff(c_32641, plain, (k2_relat_1('#skF_2')='#skF_2' | k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_32539, c_243])).
% 23.19/13.28  tff(c_32642, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(splitLeft, [status(thm)], [c_32641])).
% 23.19/13.28  tff(c_33152, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_33118, c_33118, c_32642])).
% 23.19/13.28  tff(c_196, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_153])).
% 23.19/13.28  tff(c_32542, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_32539, c_196])).
% 23.19/13.28  tff(c_33149, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_33118, c_33118, c_32542])).
% 23.19/13.28  tff(c_33162, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33118, c_88])).
% 23.19/13.28  tff(c_33158, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_33118, c_32539])).
% 23.19/13.28  tff(c_50, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.19/13.28  tff(c_94, plain, (![B_32, C_33]: (k1_relset_1(k1_xboole_0, B_32, C_33)=k1_xboole_0 | ~v1_funct_2(C_33, k1_xboole_0, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_50])).
% 23.19/13.28  tff(c_33304, plain, (![B_697, C_698]: (k1_relset_1('#skF_1', B_697, C_698)='#skF_1' | ~v1_funct_2(C_698, '#skF_1', B_697) | ~m1_subset_1(C_698, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_33158, c_33158, c_33158, c_33158, c_94])).
% 23.19/13.28  tff(c_33307, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_33162, c_33304])).
% 23.19/13.28  tff(c_33367, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_33149, c_33307])).
% 23.19/13.28  tff(c_33060, plain, (![A_684, B_685, C_686]: (k1_relset_1(A_684, B_685, C_686)=k1_relat_1(C_686) | ~m1_subset_1(C_686, k1_zfmisc_1(k2_zfmisc_1(A_684, B_685))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 23.19/13.28  tff(c_33074, plain, (![A_687]: (k1_relset_1(A_687, A_687, k6_partfun1(A_687))=k1_relat_1(k6_partfun1(A_687)))), inference(resolution, [status(thm)], [c_68, c_33060])).
% 23.19/13.28  tff(c_33089, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relset_1('#skF_2', '#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32545, c_33074])).
% 23.19/13.28  tff(c_33093, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_2')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32545, c_33089])).
% 23.19/13.28  tff(c_33126, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33118, c_33118, c_33118, c_33118, c_33093])).
% 23.19/13.28  tff(c_33416, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_33367, c_33126])).
% 23.19/13.28  tff(c_33417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33152, c_33416])).
% 23.19/13.28  tff(c_33418, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_32641])).
% 23.19/13.28  tff(c_33498, plain, (![B_707]: (v2_funct_2(B_707, k2_relat_1(B_707)) | ~v5_relat_1(B_707, k2_relat_1(B_707)) | ~v1_relat_1(B_707))), inference(cnfTransformation, [status(thm)], [f_130])).
% 23.19/13.28  tff(c_33501, plain, (v2_funct_2('#skF_2', k2_relat_1('#skF_2')) | ~v5_relat_1('#skF_2', '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_33418, c_33498])).
% 23.19/13.28  tff(c_33503, plain, (v2_funct_2('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_32640, c_33418, c_33501])).
% 23.19/13.28  tff(c_34061, plain, (v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34035, c_34035, c_33503])).
% 23.19/13.28  tff(c_32636, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_32625])).
% 23.19/13.28  tff(c_33738, plain, (![B_724, A_725]: (k2_relat_1(B_724)=A_725 | ~v2_funct_2(B_724, A_725) | ~v5_relat_1(B_724, A_725) | ~v1_relat_1(B_724))), inference(cnfTransformation, [status(thm)], [f_130])).
% 23.19/13.28  tff(c_33750, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32636, c_33738])).
% 23.19/13.28  tff(c_33762, plain, ('#skF_2'='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_33418, c_33750])).
% 23.19/13.28  tff(c_33763, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_33762])).
% 23.19/13.28  tff(c_34051, plain, (~v2_funct_2('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34035, c_33763])).
% 23.19/13.28  tff(c_34206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34061, c_34051])).
% 23.19/13.28  tff(c_34207, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_33762])).
% 23.19/13.28  tff(c_34236, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_34207, c_32545])).
% 23.19/13.28  tff(c_32550, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_32539, c_8])).
% 23.19/13.28  tff(c_34406, plain, (![A_760]: (k2_zfmisc_1(A_760, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_34207, c_32550])).
% 23.19/13.28  tff(c_34433, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34406, c_68])).
% 23.19/13.28  tff(c_34445, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34236, c_34433])).
% 23.19/13.28  tff(c_34230, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_34207, c_32550])).
% 23.19/13.28  tff(c_35736, plain, (![A_866, B_867, C_868, D_869]: (r2_relset_1(A_866, B_867, C_868, C_868) | ~m1_subset_1(D_869, k1_zfmisc_1(k2_zfmisc_1(A_866, B_867))) | ~m1_subset_1(C_868, k1_zfmisc_1(k2_zfmisc_1(A_866, B_867))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 23.19/13.28  tff(c_35738, plain, (![A_3, C_868, D_869]: (r2_relset_1(A_3, '#skF_1', C_868, C_868) | ~m1_subset_1(D_869, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_868, k1_zfmisc_1(k2_zfmisc_1(A_3, '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_34230, c_35736])).
% 23.19/13.28  tff(c_35745, plain, (![A_3, C_868, D_869]: (r2_relset_1(A_3, '#skF_1', C_868, C_868) | ~m1_subset_1(D_869, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(C_868, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34230, c_35738])).
% 23.19/13.28  tff(c_49807, plain, (![D_869]: (~m1_subset_1(D_869, k1_zfmisc_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_35745])).
% 23.19/13.28  tff(c_49840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49807, c_34445])).
% 23.19/13.28  tff(c_49842, plain, (![A_1067, C_1068]: (r2_relset_1(A_1067, '#skF_1', C_1068, C_1068) | ~m1_subset_1(C_1068, k1_zfmisc_1('#skF_1')))), inference(splitRight, [status(thm)], [c_35745])).
% 23.19/13.28  tff(c_49851, plain, (![A_1067]: (r2_relset_1(A_1067, '#skF_1', '#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_34445, c_49842])).
% 23.19/13.28  tff(c_34242, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_90])).
% 23.19/13.28  tff(c_34238, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_32532])).
% 23.19/13.28  tff(c_34240, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_86])).
% 23.19/13.28  tff(c_34239, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_235])).
% 23.19/13.28  tff(c_34227, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_34207, c_33418])).
% 23.19/13.28  tff(c_22, plain, (![A_10]: (k2_funct_1(k6_relat_1(A_10))=k6_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 23.19/13.28  tff(c_91, plain, (![A_10]: (k2_funct_1(k6_partfun1(A_10))=k6_partfun1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_22])).
% 23.19/13.28  tff(c_204, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_193, c_91])).
% 23.19/13.28  tff(c_211, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_193, c_204])).
% 23.19/13.28  tff(c_32544, plain, (k2_funct_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_32539, c_211])).
% 23.19/13.28  tff(c_34234, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_34207, c_32544])).
% 23.19/13.28  tff(c_34533, plain, (![A_770]: (k5_relat_1(k2_funct_1(A_770), A_770)=k6_partfun1(k2_relat_1(A_770)) | ~v2_funct_1(A_770) | ~v1_funct_1(A_770) | ~v1_relat_1(A_770))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18])).
% 23.19/13.28  tff(c_34542, plain, (k6_partfun1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34234, c_34533])).
% 23.19/13.28  tff(c_34549, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1' | ~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34239, c_34242, c_34236, c_34227, c_34542])).
% 23.19/13.28  tff(c_34635, plain, (~v2_funct_1('#skF_1')), inference(splitLeft, [status(thm)], [c_34549])).
% 23.19/13.28  tff(c_33585, plain, (![C_711, B_712, A_713]: (v1_xboole_0(C_711) | ~m1_subset_1(C_711, k1_zfmisc_1(k2_zfmisc_1(B_712, A_713))) | ~v1_xboole_0(A_713))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.19/13.28  tff(c_33600, plain, (![A_38]: (v1_xboole_0(k6_partfun1(A_38)) | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_68, c_33585])).
% 23.19/13.28  tff(c_33601, plain, (![A_714]: (v1_xboole_0(k6_partfun1(A_714)) | ~v1_xboole_0(A_714))), inference(resolution, [status(thm)], [c_68, c_33585])).
% 23.19/13.28  tff(c_32549, plain, (![A_55]: (A_55='#skF_2' | ~v1_xboole_0(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_142])).
% 23.19/13.28  tff(c_33618, plain, (![A_715]: (k6_partfun1(A_715)='#skF_2' | ~v1_xboole_0(A_715))), inference(resolution, [status(thm)], [c_33601, c_32549])).
% 23.19/13.28  tff(c_33625, plain, (![A_38]: (k6_partfun1(k6_partfun1(A_38))='#skF_2' | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_33600, c_33618])).
% 23.19/13.28  tff(c_34552, plain, (![A_771]: (k6_partfun1(k6_partfun1(A_771))='#skF_1' | ~v1_xboole_0(A_771))), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_33625])).
% 23.19/13.28  tff(c_35320, plain, (![A_836]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k6_partfun1(A_836), k6_partfun1(A_836)))) | ~v1_xboole_0(A_836))), inference(superposition, [status(thm), theory('equality')], [c_34552, c_68])).
% 23.19/13.28  tff(c_38, plain, (![C_30, A_28, B_29]: (v2_funct_1(C_30) | ~v3_funct_2(C_30, A_28, B_29) | ~v1_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 23.19/13.28  tff(c_35342, plain, (![A_836]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', k6_partfun1(A_836), k6_partfun1(A_836)) | ~v1_funct_1('#skF_1') | ~v1_xboole_0(A_836))), inference(resolution, [status(thm)], [c_35320, c_38])).
% 23.19/13.28  tff(c_35402, plain, (![A_836]: (v2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', k6_partfun1(A_836), k6_partfun1(A_836)) | ~v1_xboole_0(A_836))), inference(demodulation, [status(thm), theory('equality')], [c_34242, c_35342])).
% 23.19/13.28  tff(c_35422, plain, (![A_837]: (~v3_funct_2('#skF_1', k6_partfun1(A_837), k6_partfun1(A_837)) | ~v1_xboole_0(A_837))), inference(negUnitSimplification, [status(thm)], [c_34635, c_35402])).
% 23.19/13.28  tff(c_35443, plain, (~v3_funct_2('#skF_1', '#skF_1', k6_partfun1('#skF_1')) | ~v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34236, c_35422])).
% 23.19/13.28  tff(c_35449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34238, c_34240, c_34236, c_35443])).
% 23.19/13.28  tff(c_35450, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_34549])).
% 23.19/13.28  tff(c_33419, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_32641])).
% 23.19/13.28  tff(c_34226, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_34207, c_33419])).
% 23.19/13.28  tff(c_37224, plain, (![C_932, E_935, F_934, B_931, D_933, A_930]: (k1_partfun1(A_930, B_931, C_932, D_933, E_935, F_934)=k5_relat_1(E_935, F_934) | ~m1_subset_1(F_934, k1_zfmisc_1(k2_zfmisc_1(C_932, D_933))) | ~v1_funct_1(F_934) | ~m1_subset_1(E_935, k1_zfmisc_1(k2_zfmisc_1(A_930, B_931))) | ~v1_funct_1(E_935))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.19/13.28  tff(c_55142, plain, (![A_1095, B_1096, A_1097, E_1098]: (k1_partfun1(A_1095, B_1096, k1_relat_1(A_1097), k2_relat_1(A_1097), E_1098, A_1097)=k5_relat_1(E_1098, A_1097) | ~m1_subset_1(E_1098, k1_zfmisc_1(k2_zfmisc_1(A_1095, B_1096))) | ~v1_funct_1(E_1098) | ~v1_funct_1(A_1097) | ~v1_relat_1(A_1097))), inference(resolution, [status(thm)], [c_76, c_37224])).
% 23.19/13.28  tff(c_75001, plain, (![A_1259, A_1260]: (k1_partfun1(A_1259, A_1259, k1_relat_1(A_1260), k2_relat_1(A_1260), k6_partfun1(A_1259), A_1260)=k5_relat_1(k6_partfun1(A_1259), A_1260) | ~v1_funct_1(k6_partfun1(A_1259)) | ~v1_funct_1(A_1260) | ~v1_relat_1(A_1260))), inference(resolution, [status(thm)], [c_68, c_55142])).
% 23.19/13.28  tff(c_75109, plain, (![A_1259]: (k1_partfun1(A_1259, A_1259, '#skF_1', k2_relat_1('#skF_1'), k6_partfun1(A_1259), '#skF_1')=k5_relat_1(k6_partfun1(A_1259), '#skF_1') | ~v1_funct_1(k6_partfun1(A_1259)) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34226, c_75001])).
% 23.19/13.28  tff(c_96277, plain, (![A_1378]: (k1_partfun1(A_1378, A_1378, '#skF_1', '#skF_1', k6_partfun1(A_1378), '#skF_1')=k5_relat_1(k6_partfun1(A_1378), '#skF_1') | ~v1_funct_1(k6_partfun1(A_1378)))), inference(demodulation, [status(thm), theory('equality')], [c_34239, c_34242, c_34227, c_75109])).
% 23.19/13.28  tff(c_96325, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k6_partfun1('#skF_1'), '#skF_1')=k5_relat_1(k6_partfun1('#skF_1'), '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34236, c_96277])).
% 23.19/13.28  tff(c_96339, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34242, c_35450, c_34236, c_34236, c_96325])).
% 23.19/13.28  tff(c_32551, plain, (![B_4]: (k2_zfmisc_1('#skF_2', B_4)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32539, c_32539, c_10])).
% 23.19/13.28  tff(c_34374, plain, (![B_759]: (k2_zfmisc_1('#skF_1', B_759)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_34207, c_32551])).
% 23.19/13.28  tff(c_35888, plain, (![B_888, C_889]: (k1_relset_1('#skF_1', B_888, C_889)=k1_relat_1(C_889) | ~m1_subset_1(C_889, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_34374, c_32])).
% 23.19/13.28  tff(c_35890, plain, (![B_888]: (k1_relset_1('#skF_1', B_888, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_34445, c_35888])).
% 23.19/13.28  tff(c_35892, plain, (![B_888]: (k1_relset_1('#skF_1', B_888, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34226, c_35890])).
% 23.19/13.28  tff(c_34237, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_32539])).
% 23.19/13.28  tff(c_46, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_32))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 23.19/13.28  tff(c_95, plain, (![C_33, B_32]: (v1_funct_2(C_33, k1_xboole_0, B_32) | k1_relset_1(k1_xboole_0, B_32, C_33)!=k1_xboole_0 | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_46])).
% 23.19/13.28  tff(c_34465, plain, (![C_762, B_763]: (v1_funct_2(C_762, '#skF_1', B_763) | k1_relset_1('#skF_1', B_763, C_762)!='#skF_1' | ~m1_subset_1(C_762, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34237, c_34237, c_34237, c_34237, c_95])).
% 23.19/13.28  tff(c_34468, plain, (![B_763]: (v1_funct_2('#skF_1', '#skF_1', B_763) | k1_relset_1('#skF_1', B_763, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_34445, c_34465])).
% 23.19/13.28  tff(c_35894, plain, (![B_763]: (v1_funct_2('#skF_1', '#skF_1', B_763))), inference(demodulation, [status(thm), theory('equality')], [c_35892, c_34468])).
% 23.19/13.28  tff(c_35910, plain, (![A_891, B_892]: (k2_funct_2(A_891, B_892)=k2_funct_1(B_892) | ~m1_subset_1(B_892, k1_zfmisc_1(k2_zfmisc_1(A_891, A_891))) | ~v3_funct_2(B_892, A_891, A_891) | ~v1_funct_2(B_892, A_891, A_891) | ~v1_funct_1(B_892))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.19/13.28  tff(c_35921, plain, (![A_38]: (k2_funct_2(A_38, k6_partfun1(A_38))=k2_funct_1(k6_partfun1(A_38)) | ~v3_funct_2(k6_partfun1(A_38), A_38, A_38) | ~v1_funct_2(k6_partfun1(A_38), A_38, A_38) | ~v1_funct_1(k6_partfun1(A_38)))), inference(resolution, [status(thm)], [c_68, c_35910])).
% 23.19/13.28  tff(c_44481, plain, (![A_1016]: (k2_funct_2(A_1016, k6_partfun1(A_1016))=k6_partfun1(A_1016) | ~v3_funct_2(k6_partfun1(A_1016), A_1016, A_1016) | ~v1_funct_2(k6_partfun1(A_1016), A_1016, A_1016) | ~v1_funct_1(k6_partfun1(A_1016)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_35921])).
% 23.19/13.28  tff(c_44514, plain, (k2_funct_2('#skF_1', k6_partfun1('#skF_1'))=k6_partfun1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2(k6_partfun1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34236, c_44481])).
% 23.19/13.28  tff(c_44516, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34242, c_34236, c_35894, c_34236, c_34240, c_34236, c_34236, c_44514])).
% 23.19/13.28  tff(c_33488, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_32605, c_68])).
% 23.19/13.28  tff(c_12, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.19/13.28  tff(c_33507, plain, (v1_xboole_0(k6_partfun1('#skF_1')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_33488, c_12])).
% 23.19/13.28  tff(c_33510, plain, (v1_xboole_0(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32532, c_33507])).
% 23.19/13.28  tff(c_33517, plain, (k6_partfun1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_33510, c_32549])).
% 23.19/13.28  tff(c_33521, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_33517, c_187])).
% 23.19/13.28  tff(c_34216, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34207, c_34207, c_34207, c_33521])).
% 23.19/13.28  tff(c_44518, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44516, c_34216])).
% 23.19/13.28  tff(c_96340, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96339, c_44518])).
% 23.19/13.28  tff(c_96343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49851, c_96340])).
% 23.19/13.28  tff(c_96344, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_82])).
% 23.19/13.28  tff(c_98317, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98314, c_96344])).
% 23.19/13.28  tff(c_101698, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101678, c_98317])).
% 23.19/13.28  tff(c_101705, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_93, c_101698])).
% 23.19/13.28  tff(c_101708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96395, c_90, c_97171, c_98140, c_97016, c_101705])).
% 23.19/13.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.19/13.28  
% 23.19/13.28  Inference rules
% 23.19/13.28  ----------------------
% 23.19/13.28  #Ref     : 0
% 23.19/13.28  #Sup     : 29677
% 23.19/13.28  #Fact    : 0
% 23.19/13.28  #Define  : 0
% 23.19/13.28  #Split   : 69
% 23.19/13.28  #Chain   : 0
% 23.19/13.28  #Close   : 0
% 23.19/13.28  
% 23.19/13.28  Ordering : KBO
% 23.19/13.28  
% 23.19/13.28  Simplification rules
% 23.19/13.28  ----------------------
% 23.19/13.28  #Subsume      : 10003
% 23.19/13.28  #Demod        : 17974
% 23.19/13.28  #Tautology    : 5573
% 23.19/13.28  #SimpNegUnit  : 129
% 23.19/13.28  #BackRed      : 397
% 23.19/13.28  
% 23.19/13.28  #Partial instantiations: 0
% 23.19/13.28  #Strategies tried      : 1
% 23.19/13.28  
% 23.19/13.28  Timing (in seconds)
% 23.19/13.28  ----------------------
% 23.33/13.28  Preprocessing        : 0.36
% 23.33/13.28  Parsing              : 0.19
% 23.33/13.28  CNF conversion       : 0.02
% 23.33/13.28  Main loop            : 12.08
% 23.33/13.28  Inferencing          : 2.10
% 23.33/13.28  Reduction            : 4.16
% 23.33/13.28  Demodulation         : 3.29
% 23.33/13.28  BG Simplification    : 0.29
% 23.33/13.28  Subsumption          : 4.64
% 23.33/13.28  Abstraction          : 0.37
% 23.33/13.29  MUC search           : 0.00
% 23.33/13.29  Cooper               : 0.00
% 23.33/13.29  Total                : 12.55
% 23.33/13.29  Index Insertion      : 0.00
% 23.33/13.29  Index Deletion       : 0.00
% 23.33/13.29  Index Matching       : 0.00
% 23.33/13.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
