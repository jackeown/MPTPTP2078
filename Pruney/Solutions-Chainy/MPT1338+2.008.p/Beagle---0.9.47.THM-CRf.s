%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:14 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  220 (10776 expanded)
%              Number of leaves         :   44 (3767 expanded)
%              Depth                    :   23
%              Number of atoms          :  468 (33063 expanded)
%              Number of equality atoms :  117 (10703 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_120,axiom,(
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

tff(f_130,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_79,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_74,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_76,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_84,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_76])).

tff(c_70,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_83,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_76])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_114,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_64])).

tff(c_10,plain,(
    ! [C_5,A_3,B_4] :
      ( v1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_6,plain,(
    ! [A_2] :
      ( k2_relat_1(k2_funct_1(A_2)) = k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1249,plain,(
    ! [C_150,A_151,B_152] :
      ( v4_relat_1(C_150,A_151)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1253,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_114,c_1249])).

tff(c_1281,plain,(
    ! [B_162,A_163] :
      ( k1_relat_1(B_162) = A_163
      | ~ v1_partfun1(B_162,A_163)
      | ~ v4_relat_1(B_162,A_163)
      | ~ v1_relat_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1284,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1253,c_1281])).

tff(c_1287,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1284])).

tff(c_1292,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1287])).

tff(c_1357,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1365,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_1357])).

tff(c_62,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_109,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83,c_62])).

tff(c_1366,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_109])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_89,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_66])).

tff(c_90,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_89])).

tff(c_1377,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_90])).

tff(c_1375,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_114])).

tff(c_1476,plain,(
    ! [B_190,C_191,A_192] :
      ( k1_xboole_0 = B_190
      | v1_partfun1(C_191,A_192)
      | ~ v1_funct_2(C_191,A_192,B_190)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_190)))
      | ~ v1_funct_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1479,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1375,c_1476])).

tff(c_1485,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1377,c_1479])).

tff(c_1486,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1292,c_1485])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_95,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_95])).

tff(c_105,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_101])).

tff(c_106,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_105])).

tff(c_1376,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1366,c_106])).

tff(c_1496,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1486,c_1376])).

tff(c_1500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1496])).

tff(c_1501,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1287])).

tff(c_1506,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_114])).

tff(c_1601,plain,(
    ! [A_196,B_197,C_198] :
      ( k2_relset_1(A_196,B_197,C_198) = k2_relat_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1609,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1506,c_1601])).

tff(c_1507,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_109])).

tff(c_1631,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1609,c_1507])).

tff(c_1509,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_90])).

tff(c_1638,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1509])).

tff(c_1636,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1609])).

tff(c_1637,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1506])).

tff(c_1872,plain,(
    ! [C_240,B_241,A_242] :
      ( m1_subset_1(k2_funct_1(C_240),k1_zfmisc_1(k2_zfmisc_1(B_241,A_242)))
      | k2_relset_1(A_242,B_241,C_240) != B_241
      | ~ v2_funct_1(C_240)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_242,B_241)))
      | ~ v1_funct_2(C_240,A_242,B_241)
      | ~ v1_funct_1(C_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2083,plain,(
    ! [C_247,A_248,B_249] :
      ( v1_relat_1(k2_funct_1(C_247))
      | k2_relset_1(A_248,B_249,C_247) != B_249
      | ~ v2_funct_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ v1_funct_2(C_247,A_248,B_249)
      | ~ v1_funct_1(C_247) ) ),
    inference(resolution,[status(thm)],[c_1872,c_10])).

tff(c_2095,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1637,c_2083])).

tff(c_2104,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1638,c_60,c_1636,c_2095])).

tff(c_1784,plain,(
    ! [C_225,A_226,B_227] :
      ( v1_funct_1(k2_funct_1(C_225))
      | k2_relset_1(A_226,B_227,C_225) != B_227
      | ~ v2_funct_1(C_225)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_2(C_225,A_226,B_227)
      | ~ v1_funct_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1787,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1637,c_1784])).

tff(c_1793,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1638,c_60,c_1636,c_1787])).

tff(c_8,plain,(
    ! [A_2] :
      ( k1_relat_1(k2_funct_1(A_2)) = k2_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1578,plain,(
    ! [A_195] :
      ( m1_subset_1(A_195,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_195),k2_relat_1(A_195))))
      | ~ v1_funct_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_14,plain,(
    ! [C_8,A_6,B_7] :
      ( v4_relat_1(C_8,A_6)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1614,plain,(
    ! [A_200] :
      ( v4_relat_1(A_200,k1_relat_1(A_200))
      | ~ v1_funct_1(A_200)
      | ~ v1_relat_1(A_200) ) ),
    inference(resolution,[status(thm)],[c_1578,c_14])).

tff(c_32,plain,(
    ! [B_20] :
      ( v1_partfun1(B_20,k1_relat_1(B_20))
      | ~ v4_relat_1(B_20,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1627,plain,(
    ! [A_201] :
      ( v1_partfun1(A_201,k1_relat_1(A_201))
      | ~ v1_funct_1(A_201)
      | ~ v1_relat_1(A_201) ) ),
    inference(resolution,[status(thm)],[c_1614,c_32])).

tff(c_1630,plain,(
    ! [A_2] :
      ( v1_partfun1(k2_funct_1(A_2),k2_relat_1(A_2))
      | ~ v1_funct_1(k2_funct_1(A_2))
      | ~ v1_relat_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1627])).

tff(c_2141,plain,(
    ! [C_253,B_254,A_255] :
      ( v4_relat_1(k2_funct_1(C_253),B_254)
      | k2_relset_1(A_255,B_254,C_253) != B_254
      | ~ v2_funct_1(C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_255,B_254)))
      | ~ v1_funct_2(C_253,A_255,B_254)
      | ~ v1_funct_1(C_253) ) ),
    inference(resolution,[status(thm)],[c_1872,c_14])).

tff(c_2153,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1637,c_2141])).

tff(c_2162,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1638,c_60,c_1636,c_2153])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( k1_relat_1(B_20) = A_19
      | ~ v1_partfun1(B_20,A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2166,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2162,c_34])).

tff(c_2169,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2104,c_2166])).

tff(c_2170,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2169])).

tff(c_2173,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1630,c_2170])).

tff(c_2177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68,c_60,c_2104,c_1793,c_2173])).

tff(c_2178,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2169])).

tff(c_1596,plain,(
    ! [A_2] :
      ( m1_subset_1(k2_funct_1(A_2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_2)),k1_relat_1(A_2))))
      | ~ v1_funct_1(k2_funct_1(A_2))
      | ~ v1_relat_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1578])).

tff(c_2183,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2178,c_1596])).

tff(c_2235,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68,c_60,c_2104,c_1793,c_2183])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( k2_relset_1(A_13,B_14,C_15) = k2_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2379,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2235,c_18])).

tff(c_1851,plain,(
    ! [A_237,B_238,C_239] :
      ( k2_tops_2(A_237,B_238,C_239) = k2_funct_1(C_239)
      | ~ v2_funct_1(C_239)
      | k2_relset_1(A_237,B_238,C_239) != B_238
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_2(C_239,A_237,B_238)
      | ~ v1_funct_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1854,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1637,c_1851])).

tff(c_1860,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1638,c_1636,c_60,c_1854])).

tff(c_121,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_114,c_121])).

tff(c_153,plain,(
    ! [B_55,A_56] :
      ( k1_relat_1(B_55) = A_56
      | ~ v1_partfun1(B_55,A_56)
      | ~ v4_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_156,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_153])).

tff(c_159,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_156])).

tff(c_160,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_221,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_229,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_221])).

tff(c_230,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_109])).

tff(c_240,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_90])).

tff(c_238,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_114])).

tff(c_323,plain,(
    ! [B_80,C_81,A_82] :
      ( k1_xboole_0 = B_80
      | v1_partfun1(C_81,A_82)
      | ~ v1_funct_2(C_81,A_82,B_80)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_80)))
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_326,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_238,c_323])).

tff(c_332,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_240,c_326])).

tff(c_333,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_332])).

tff(c_239,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_106])).

tff(c_341,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_239])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_341])).

tff(c_346,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_350,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_114])).

tff(c_468,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_476,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_350,c_468])).

tff(c_351,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_109])).

tff(c_477,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_351])).

tff(c_353,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_90])).

tff(c_484,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_353])).

tff(c_482,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_476])).

tff(c_483,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_350])).

tff(c_672,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_tops_2(A_124,B_125,C_126) = k2_funct_1(C_126)
      | ~ v2_funct_1(C_126)
      | k2_relset_1(A_124,B_125,C_126) != B_125
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_2(C_126,A_124,B_125)
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_675,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_672])).

tff(c_681,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_484,c_482,c_60,c_675])).

tff(c_58,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_119,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84,c_83,c_83,c_84,c_84,c_83,c_83,c_58])).

tff(c_120,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_348,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_346,c_120])).

tff(c_564,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_477,c_477,c_348])).

tff(c_683,plain,(
    k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_564])).

tff(c_642,plain,(
    ! [C_119,B_120,A_121] :
      ( v1_funct_2(k2_funct_1(C_119),B_120,A_121)
      | k2_relset_1(A_121,B_120,C_119) != B_120
      | ~ v2_funct_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120)))
      | ~ v1_funct_2(C_119,A_121,B_120)
      | ~ v1_funct_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_645,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_642])).

tff(c_651,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_484,c_60,c_482,c_645])).

tff(c_706,plain,(
    ! [C_130,B_131,A_132] :
      ( m1_subset_1(k2_funct_1(C_130),k1_zfmisc_1(k2_zfmisc_1(B_131,A_132)))
      | k2_relset_1(A_132,B_131,C_130) != B_131
      | ~ v2_funct_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131)))
      | ~ v1_funct_2(C_130,A_132,B_131)
      | ~ v1_funct_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_917,plain,(
    ! [C_137,A_138,B_139] :
      ( v1_relat_1(k2_funct_1(C_137))
      | k2_relset_1(A_138,B_139,C_137) != B_139
      | ~ v2_funct_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_2(C_137,A_138,B_139)
      | ~ v1_funct_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_706,c_10])).

tff(c_929,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_917])).

tff(c_938,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_484,c_60,c_482,c_929])).

tff(c_607,plain,(
    ! [C_112,A_113,B_114] :
      ( v1_funct_1(k2_funct_1(C_112))
      | k2_relset_1(A_113,B_114,C_112) != B_114
      | ~ v2_funct_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_2(C_112,A_113,B_114)
      | ~ v1_funct_1(C_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_610,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_607])).

tff(c_616,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_484,c_60,c_482,c_610])).

tff(c_420,plain,(
    ! [A_84] :
      ( m1_subset_1(A_84,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_84),k2_relat_1(A_84))))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_447,plain,(
    ! [A_86] :
      ( v4_relat_1(A_86,k1_relat_1(A_86))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_420,c_14])).

tff(c_460,plain,(
    ! [A_87] :
      ( v1_partfun1(A_87,k1_relat_1(A_87))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_447,c_32])).

tff(c_463,plain,(
    ! [A_2] :
      ( v1_partfun1(k2_funct_1(A_2),k2_relat_1(A_2))
      | ~ v1_funct_1(k2_funct_1(A_2))
      | ~ v1_relat_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_460])).

tff(c_980,plain,(
    ! [C_144,B_145,A_146] :
      ( v4_relat_1(k2_funct_1(C_144),B_145)
      | k2_relset_1(A_146,B_145,C_144) != B_145
      | ~ v2_funct_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_146,B_145)))
      | ~ v1_funct_2(C_144,A_146,B_145)
      | ~ v1_funct_1(C_144) ) ),
    inference(resolution,[status(thm)],[c_706,c_14])).

tff(c_992,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_483,c_980])).

tff(c_1001,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_484,c_60,c_482,c_992])).

tff(c_1005,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1001,c_34])).

tff(c_1008,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_938,c_1005])).

tff(c_1009,plain,(
    ~ v1_partfun1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_1012,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_463,c_1009])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68,c_60,c_938,c_616,c_1012])).

tff(c_1017,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_435,plain,(
    ! [A_2] :
      ( m1_subset_1(k2_funct_1(A_2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_2)),k1_relat_1(A_2))))
      | ~ v1_funct_1(k2_funct_1(A_2))
      | ~ v1_relat_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_420])).

tff(c_1025,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_435])).

tff(c_1079,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68,c_60,c_938,c_616,c_1025])).

tff(c_30,plain,(
    ! [B_17,A_16,C_18] :
      ( k1_xboole_0 = B_17
      | k1_relset_1(A_16,B_17,C_18) = A_16
      | ~ v1_funct_2(C_18,A_16,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1173,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1079,c_30])).

tff(c_1217,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_1173])).

tff(c_1218,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_1217])).

tff(c_98,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_95])).

tff(c_103,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_98])).

tff(c_107,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_352,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_107])).

tff(c_1242,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1218,c_352])).

tff(c_1246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1242])).

tff(c_1247,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_1505,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_1501,c_1501,c_1247])).

tff(c_1727,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1631,c_1631,c_1505])).

tff(c_1862,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1860,c_1727])).

tff(c_2510,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2379,c_1862])).

tff(c_2517,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2510])).

tff(c_2521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_68,c_60,c_2517])).

tff(c_2523,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_2524,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_84,c_64])).

tff(c_2547,plain,(
    ! [C_271,A_272,B_273] :
      ( v1_xboole_0(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273)))
      | ~ v1_xboole_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2550,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2524,c_2547])).

tff(c_2553,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2523,c_2550])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(k2_relat_1(A_1))
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2594,plain,(
    ! [A_280,B_281,C_282] :
      ( k2_relset_1(A_280,B_281,C_282) = k2_relat_1(C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_280,B_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2598,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2524,c_2594])).

tff(c_2525,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_84,c_62])).

tff(c_2599,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2598,c_2525])).

tff(c_2608,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2599,c_106])).

tff(c_2617,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_2608])).

tff(c_2621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2553,c_2617])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:09:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.85  
% 4.69/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.69/1.86  
% 4.69/1.86  %Foreground sorts:
% 4.69/1.86  
% 4.69/1.86  
% 4.69/1.86  %Background operators:
% 4.69/1.86  
% 4.69/1.86  
% 4.69/1.86  %Foreground operators:
% 4.69/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.69/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.69/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.69/1.86  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.69/1.86  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.69/1.86  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 4.69/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.69/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.69/1.86  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.69/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.69/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.69/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.69/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.69/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.69/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.69/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.69/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.69/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.69/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.69/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/1.86  
% 4.69/1.89  tff(f_178, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 4.69/1.89  tff(f_134, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.69/1.89  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.69/1.89  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.69/1.89  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.69/1.89  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.69/1.89  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.69/1.89  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.69/1.89  tff(f_104, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 4.69/1.89  tff(f_142, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.69/1.89  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.69/1.89  tff(f_130, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.69/1.89  tff(f_154, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 4.69/1.89  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.69/1.89  tff(f_57, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.69/1.89  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 4.69/1.89  tff(c_74, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_76, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.69/1.89  tff(c_84, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_76])).
% 4.69/1.89  tff(c_70, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_83, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_76])).
% 4.69/1.89  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_114, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_64])).
% 4.69/1.89  tff(c_10, plain, (![C_5, A_3, B_4]: (v1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.69/1.89  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_10])).
% 4.69/1.89  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_6, plain, (![A_2]: (k2_relat_1(k2_funct_1(A_2))=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.69/1.89  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.69/1.89  tff(c_1249, plain, (![C_150, A_151, B_152]: (v4_relat_1(C_150, A_151) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.69/1.89  tff(c_1253, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_114, c_1249])).
% 4.69/1.89  tff(c_1281, plain, (![B_162, A_163]: (k1_relat_1(B_162)=A_163 | ~v1_partfun1(B_162, A_163) | ~v4_relat_1(B_162, A_163) | ~v1_relat_1(B_162))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.69/1.89  tff(c_1284, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1253, c_1281])).
% 4.69/1.89  tff(c_1287, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_1284])).
% 4.69/1.89  tff(c_1292, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1287])).
% 4.69/1.89  tff(c_1357, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.69/1.89  tff(c_1365, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_1357])).
% 4.69/1.89  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_109, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83, c_62])).
% 4.69/1.89  tff(c_1366, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_109])).
% 4.69/1.89  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_89, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_66])).
% 4.69/1.89  tff(c_90, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_89])).
% 4.69/1.89  tff(c_1377, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_90])).
% 4.69/1.89  tff(c_1375, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_114])).
% 4.69/1.89  tff(c_1476, plain, (![B_190, C_191, A_192]: (k1_xboole_0=B_190 | v1_partfun1(C_191, A_192) | ~v1_funct_2(C_191, A_192, B_190) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_190))) | ~v1_funct_1(C_191))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.69/1.89  tff(c_1479, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1375, c_1476])).
% 4.69/1.89  tff(c_1485, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1377, c_1479])).
% 4.69/1.89  tff(c_1486, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1292, c_1485])).
% 4.69/1.89  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_95, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.69/1.89  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_83, c_95])).
% 4.69/1.89  tff(c_105, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_101])).
% 4.69/1.89  tff(c_106, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_105])).
% 4.69/1.89  tff(c_1376, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1366, c_106])).
% 4.69/1.89  tff(c_1496, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1486, c_1376])).
% 4.69/1.89  tff(c_1500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1496])).
% 4.69/1.89  tff(c_1501, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1287])).
% 4.69/1.89  tff(c_1506, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_114])).
% 4.69/1.89  tff(c_1601, plain, (![A_196, B_197, C_198]: (k2_relset_1(A_196, B_197, C_198)=k2_relat_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.69/1.89  tff(c_1609, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1506, c_1601])).
% 4.69/1.89  tff(c_1507, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_109])).
% 4.69/1.89  tff(c_1631, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1609, c_1507])).
% 4.69/1.89  tff(c_1509, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_90])).
% 4.69/1.89  tff(c_1638, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1509])).
% 4.69/1.89  tff(c_1636, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1609])).
% 4.69/1.89  tff(c_1637, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1506])).
% 4.69/1.89  tff(c_1872, plain, (![C_240, B_241, A_242]: (m1_subset_1(k2_funct_1(C_240), k1_zfmisc_1(k2_zfmisc_1(B_241, A_242))) | k2_relset_1(A_242, B_241, C_240)!=B_241 | ~v2_funct_1(C_240) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_242, B_241))) | ~v1_funct_2(C_240, A_242, B_241) | ~v1_funct_1(C_240))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.89  tff(c_2083, plain, (![C_247, A_248, B_249]: (v1_relat_1(k2_funct_1(C_247)) | k2_relset_1(A_248, B_249, C_247)!=B_249 | ~v2_funct_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~v1_funct_2(C_247, A_248, B_249) | ~v1_funct_1(C_247))), inference(resolution, [status(thm)], [c_1872, c_10])).
% 4.69/1.89  tff(c_2095, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1637, c_2083])).
% 4.69/1.89  tff(c_2104, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1638, c_60, c_1636, c_2095])).
% 4.69/1.89  tff(c_1784, plain, (![C_225, A_226, B_227]: (v1_funct_1(k2_funct_1(C_225)) | k2_relset_1(A_226, B_227, C_225)!=B_227 | ~v2_funct_1(C_225) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_2(C_225, A_226, B_227) | ~v1_funct_1(C_225))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.89  tff(c_1787, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1637, c_1784])).
% 4.69/1.89  tff(c_1793, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1638, c_60, c_1636, c_1787])).
% 4.69/1.89  tff(c_8, plain, (![A_2]: (k1_relat_1(k2_funct_1(A_2))=k2_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.69/1.89  tff(c_1578, plain, (![A_195]: (m1_subset_1(A_195, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_195), k2_relat_1(A_195)))) | ~v1_funct_1(A_195) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.69/1.89  tff(c_14, plain, (![C_8, A_6, B_7]: (v4_relat_1(C_8, A_6) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.69/1.89  tff(c_1614, plain, (![A_200]: (v4_relat_1(A_200, k1_relat_1(A_200)) | ~v1_funct_1(A_200) | ~v1_relat_1(A_200))), inference(resolution, [status(thm)], [c_1578, c_14])).
% 4.69/1.89  tff(c_32, plain, (![B_20]: (v1_partfun1(B_20, k1_relat_1(B_20)) | ~v4_relat_1(B_20, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.69/1.89  tff(c_1627, plain, (![A_201]: (v1_partfun1(A_201, k1_relat_1(A_201)) | ~v1_funct_1(A_201) | ~v1_relat_1(A_201))), inference(resolution, [status(thm)], [c_1614, c_32])).
% 4.69/1.89  tff(c_1630, plain, (![A_2]: (v1_partfun1(k2_funct_1(A_2), k2_relat_1(A_2)) | ~v1_funct_1(k2_funct_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1627])).
% 4.69/1.89  tff(c_2141, plain, (![C_253, B_254, A_255]: (v4_relat_1(k2_funct_1(C_253), B_254) | k2_relset_1(A_255, B_254, C_253)!=B_254 | ~v2_funct_1(C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_255, B_254))) | ~v1_funct_2(C_253, A_255, B_254) | ~v1_funct_1(C_253))), inference(resolution, [status(thm)], [c_1872, c_14])).
% 4.69/1.89  tff(c_2153, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1637, c_2141])).
% 4.69/1.89  tff(c_2162, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1638, c_60, c_1636, c_2153])).
% 4.69/1.89  tff(c_34, plain, (![B_20, A_19]: (k1_relat_1(B_20)=A_19 | ~v1_partfun1(B_20, A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.69/1.89  tff(c_2166, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2162, c_34])).
% 4.69/1.89  tff(c_2169, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2104, c_2166])).
% 4.69/1.89  tff(c_2170, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2169])).
% 4.69/1.89  tff(c_2173, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1630, c_2170])).
% 4.69/1.89  tff(c_2177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_68, c_60, c_2104, c_1793, c_2173])).
% 4.69/1.89  tff(c_2178, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2169])).
% 4.69/1.89  tff(c_1596, plain, (![A_2]: (m1_subset_1(k2_funct_1(A_2), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_2)), k1_relat_1(A_2)))) | ~v1_funct_1(k2_funct_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1578])).
% 4.69/1.89  tff(c_2183, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2178, c_1596])).
% 4.69/1.89  tff(c_2235, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_68, c_60, c_2104, c_1793, c_2183])).
% 4.69/1.89  tff(c_18, plain, (![A_13, B_14, C_15]: (k2_relset_1(A_13, B_14, C_15)=k2_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.69/1.89  tff(c_2379, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2235, c_18])).
% 4.69/1.89  tff(c_1851, plain, (![A_237, B_238, C_239]: (k2_tops_2(A_237, B_238, C_239)=k2_funct_1(C_239) | ~v2_funct_1(C_239) | k2_relset_1(A_237, B_238, C_239)!=B_238 | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~v1_funct_2(C_239, A_237, B_238) | ~v1_funct_1(C_239))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.89  tff(c_1854, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1637, c_1851])).
% 4.69/1.89  tff(c_1860, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1638, c_1636, c_60, c_1854])).
% 4.69/1.89  tff(c_121, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.69/1.89  tff(c_125, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_114, c_121])).
% 4.69/1.89  tff(c_153, plain, (![B_55, A_56]: (k1_relat_1(B_55)=A_56 | ~v1_partfun1(B_55, A_56) | ~v4_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.69/1.89  tff(c_156, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_125, c_153])).
% 4.69/1.89  tff(c_159, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_156])).
% 4.69/1.89  tff(c_160, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_159])).
% 4.69/1.89  tff(c_221, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.69/1.89  tff(c_229, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_221])).
% 4.69/1.89  tff(c_230, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_229, c_109])).
% 4.69/1.89  tff(c_240, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_90])).
% 4.69/1.89  tff(c_238, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_114])).
% 4.69/1.89  tff(c_323, plain, (![B_80, C_81, A_82]: (k1_xboole_0=B_80 | v1_partfun1(C_81, A_82) | ~v1_funct_2(C_81, A_82, B_80) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_80))) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.69/1.89  tff(c_326, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_238, c_323])).
% 4.69/1.89  tff(c_332, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_240, c_326])).
% 4.69/1.89  tff(c_333, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_160, c_332])).
% 4.69/1.89  tff(c_239, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_106])).
% 4.69/1.89  tff(c_341, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_333, c_239])).
% 4.69/1.89  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_341])).
% 4.69/1.89  tff(c_346, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_159])).
% 4.69/1.89  tff(c_350, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_114])).
% 4.69/1.89  tff(c_468, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.69/1.89  tff(c_476, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_350, c_468])).
% 4.69/1.89  tff(c_351, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_109])).
% 4.69/1.89  tff(c_477, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_351])).
% 4.69/1.89  tff(c_353, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_90])).
% 4.69/1.89  tff(c_484, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_353])).
% 4.69/1.89  tff(c_482, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_476])).
% 4.69/1.89  tff(c_483, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_350])).
% 4.69/1.89  tff(c_672, plain, (![A_124, B_125, C_126]: (k2_tops_2(A_124, B_125, C_126)=k2_funct_1(C_126) | ~v2_funct_1(C_126) | k2_relset_1(A_124, B_125, C_126)!=B_125 | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_2(C_126, A_124, B_125) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.69/1.89  tff(c_675, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_483, c_672])).
% 4.69/1.89  tff(c_681, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_484, c_482, c_60, c_675])).
% 4.69/1.89  tff(c_58, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.69/1.89  tff(c_119, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_84, c_83, c_83, c_84, c_84, c_83, c_83, c_58])).
% 4.69/1.89  tff(c_120, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_119])).
% 4.69/1.89  tff(c_348, plain, (k1_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_346, c_120])).
% 4.69/1.89  tff(c_564, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_477, c_477, c_477, c_348])).
% 4.69/1.89  tff(c_683, plain, (k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_564])).
% 4.69/1.89  tff(c_642, plain, (![C_119, B_120, A_121]: (v1_funct_2(k2_funct_1(C_119), B_120, A_121) | k2_relset_1(A_121, B_120, C_119)!=B_120 | ~v2_funct_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))) | ~v1_funct_2(C_119, A_121, B_120) | ~v1_funct_1(C_119))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.89  tff(c_645, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_483, c_642])).
% 4.69/1.89  tff(c_651, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_484, c_60, c_482, c_645])).
% 4.69/1.89  tff(c_706, plain, (![C_130, B_131, A_132]: (m1_subset_1(k2_funct_1(C_130), k1_zfmisc_1(k2_zfmisc_1(B_131, A_132))) | k2_relset_1(A_132, B_131, C_130)!=B_131 | ~v2_funct_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))) | ~v1_funct_2(C_130, A_132, B_131) | ~v1_funct_1(C_130))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.89  tff(c_917, plain, (![C_137, A_138, B_139]: (v1_relat_1(k2_funct_1(C_137)) | k2_relset_1(A_138, B_139, C_137)!=B_139 | ~v2_funct_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_2(C_137, A_138, B_139) | ~v1_funct_1(C_137))), inference(resolution, [status(thm)], [c_706, c_10])).
% 4.69/1.89  tff(c_929, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_483, c_917])).
% 4.69/1.89  tff(c_938, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_484, c_60, c_482, c_929])).
% 4.69/1.89  tff(c_607, plain, (![C_112, A_113, B_114]: (v1_funct_1(k2_funct_1(C_112)) | k2_relset_1(A_113, B_114, C_112)!=B_114 | ~v2_funct_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_2(C_112, A_113, B_114) | ~v1_funct_1(C_112))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.89  tff(c_610, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_483, c_607])).
% 4.69/1.89  tff(c_616, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_484, c_60, c_482, c_610])).
% 4.69/1.89  tff(c_420, plain, (![A_84]: (m1_subset_1(A_84, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_84), k2_relat_1(A_84)))) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.69/1.89  tff(c_447, plain, (![A_86]: (v4_relat_1(A_86, k1_relat_1(A_86)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_420, c_14])).
% 4.69/1.89  tff(c_460, plain, (![A_87]: (v1_partfun1(A_87, k1_relat_1(A_87)) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_447, c_32])).
% 4.69/1.89  tff(c_463, plain, (![A_2]: (v1_partfun1(k2_funct_1(A_2), k2_relat_1(A_2)) | ~v1_funct_1(k2_funct_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_8, c_460])).
% 4.69/1.89  tff(c_980, plain, (![C_144, B_145, A_146]: (v4_relat_1(k2_funct_1(C_144), B_145) | k2_relset_1(A_146, B_145, C_144)!=B_145 | ~v2_funct_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_146, B_145))) | ~v1_funct_2(C_144, A_146, B_145) | ~v1_funct_1(C_144))), inference(resolution, [status(thm)], [c_706, c_14])).
% 4.69/1.89  tff(c_992, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_483, c_980])).
% 4.69/1.89  tff(c_1001, plain, (v4_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_484, c_60, c_482, c_992])).
% 4.69/1.89  tff(c_1005, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1001, c_34])).
% 4.69/1.89  tff(c_1008, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_938, c_1005])).
% 4.69/1.89  tff(c_1009, plain, (~v1_partfun1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1008])).
% 4.69/1.89  tff(c_1012, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_463, c_1009])).
% 4.69/1.89  tff(c_1016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_68, c_60, c_938, c_616, c_1012])).
% 4.69/1.89  tff(c_1017, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1008])).
% 4.69/1.89  tff(c_435, plain, (![A_2]: (m1_subset_1(k2_funct_1(A_2), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_2)), k1_relat_1(A_2)))) | ~v1_funct_1(k2_funct_1(A_2)) | ~v1_relat_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_6, c_420])).
% 4.69/1.89  tff(c_1025, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1017, c_435])).
% 4.69/1.89  tff(c_1079, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_68, c_60, c_938, c_616, c_1025])).
% 4.69/1.89  tff(c_30, plain, (![B_17, A_16, C_18]: (k1_xboole_0=B_17 | k1_relset_1(A_16, B_17, C_18)=A_16 | ~v1_funct_2(C_18, A_16, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.89  tff(c_1173, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1079, c_30])).
% 4.69/1.89  tff(c_1217, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_651, c_1173])).
% 4.69/1.89  tff(c_1218, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_683, c_1217])).
% 4.69/1.89  tff(c_98, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_84, c_95])).
% 4.69/1.89  tff(c_103, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_98])).
% 4.69/1.89  tff(c_107, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_103])).
% 4.69/1.89  tff(c_352, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_107])).
% 4.69/1.89  tff(c_1242, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1218, c_352])).
% 4.69/1.89  tff(c_1246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1242])).
% 4.69/1.89  tff(c_1247, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_119])).
% 4.69/1.89  tff(c_1505, plain, (k2_relset_1(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_1501, c_1501, c_1247])).
% 4.69/1.89  tff(c_1727, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1631, c_1631, c_1505])).
% 4.69/1.89  tff(c_1862, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1860, c_1727])).
% 4.69/1.89  tff(c_2510, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2379, c_1862])).
% 4.69/1.89  tff(c_2517, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_2510])).
% 4.69/1.89  tff(c_2521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_68, c_60, c_2517])).
% 4.69/1.89  tff(c_2523, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_103])).
% 4.69/1.89  tff(c_2524, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_84, c_64])).
% 4.69/1.89  tff(c_2547, plain, (![C_271, A_272, B_273]: (v1_xboole_0(C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))) | ~v1_xboole_0(A_272))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.69/1.89  tff(c_2550, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2524, c_2547])).
% 4.69/1.89  tff(c_2553, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2523, c_2550])).
% 4.69/1.89  tff(c_4, plain, (![A_1]: (v1_xboole_0(k2_relat_1(A_1)) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.69/1.89  tff(c_2594, plain, (![A_280, B_281, C_282]: (k2_relset_1(A_280, B_281, C_282)=k2_relat_1(C_282) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_280, B_281))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.69/1.89  tff(c_2598, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2524, c_2594])).
% 4.69/1.89  tff(c_2525, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_84, c_62])).
% 4.69/1.89  tff(c_2599, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2598, c_2525])).
% 4.69/1.89  tff(c_2608, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2599, c_106])).
% 4.69/1.89  tff(c_2617, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_2608])).
% 4.69/1.89  tff(c_2621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2553, c_2617])).
% 4.69/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.89  
% 4.69/1.89  Inference rules
% 4.69/1.89  ----------------------
% 4.69/1.89  #Ref     : 0
% 4.69/1.89  #Sup     : 558
% 4.69/1.89  #Fact    : 0
% 4.69/1.89  #Define  : 0
% 4.69/1.89  #Split   : 12
% 4.69/1.89  #Chain   : 0
% 4.69/1.89  #Close   : 0
% 4.69/1.89  
% 4.69/1.89  Ordering : KBO
% 4.69/1.89  
% 4.69/1.89  Simplification rules
% 4.69/1.89  ----------------------
% 4.69/1.89  #Subsume      : 71
% 4.69/1.89  #Demod        : 518
% 4.69/1.89  #Tautology    : 200
% 4.69/1.89  #SimpNegUnit  : 17
% 4.69/1.89  #BackRed      : 91
% 4.69/1.89  
% 4.69/1.89  #Partial instantiations: 0
% 4.69/1.89  #Strategies tried      : 1
% 4.69/1.89  
% 4.69/1.89  Timing (in seconds)
% 4.69/1.89  ----------------------
% 4.69/1.89  Preprocessing        : 0.37
% 4.69/1.89  Parsing              : 0.21
% 4.69/1.89  CNF conversion       : 0.02
% 4.69/1.89  Main loop            : 0.67
% 4.69/1.89  Inferencing          : 0.26
% 4.69/1.89  Reduction            : 0.21
% 4.69/1.89  Demodulation         : 0.15
% 4.69/1.89  BG Simplification    : 0.03
% 4.69/1.89  Subsumption          : 0.11
% 4.69/1.89  Abstraction          : 0.03
% 4.69/1.89  MUC search           : 0.00
% 4.69/1.89  Cooper               : 0.00
% 4.69/1.89  Total                : 1.11
% 4.69/1.89  Index Insertion      : 0.00
% 4.69/1.89  Index Deletion       : 0.00
% 4.69/1.89  Index Matching       : 0.00
% 4.69/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
