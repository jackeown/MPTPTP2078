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
% DateTime   : Thu Dec  3 10:11:07 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.61s
% Verified   : 
% Statistics : Number of formulae       :  186 (1060 expanded)
%              Number of leaves         :   41 ( 358 expanded)
%              Depth                    :   12
%              Number of atoms          :  333 (3158 expanded)
%              Number of equality atoms :   68 ( 837 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3934,plain,(
    ! [C_352,A_353,B_354] :
      ( v1_relat_1(C_352)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3943,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3934])).

tff(c_4046,plain,(
    ! [C_372,A_373,B_374] :
      ( v4_relat_1(C_372,A_373)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4055,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_4046])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4185,plain,(
    ! [A_390,B_391,C_392] :
      ( k2_relset_1(A_390,B_391,C_392) = k2_relat_1(C_392)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4194,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_4185])).

tff(c_56,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4195,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4194,c_56])).

tff(c_4807,plain,(
    ! [C_452,A_453,B_454] :
      ( m1_subset_1(C_452,k1_zfmisc_1(k2_zfmisc_1(A_453,B_454)))
      | ~ r1_tarski(k2_relat_1(C_452),B_454)
      | ~ r1_tarski(k1_relat_1(C_452),A_453)
      | ~ v1_relat_1(C_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_143,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_152,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_143])).

tff(c_237,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_246,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_237])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_393,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_402,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_393])).

tff(c_1160,plain,(
    ! [B_170,A_171,C_172] :
      ( k1_xboole_0 = B_170
      | k1_relset_1(A_171,B_170,C_172) = A_171
      | ~ v1_funct_2(C_172,A_171,B_170)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_171,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1170,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1160])).

tff(c_1175,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_402,c_1170])).

tff(c_1176,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1175])).

tff(c_1223,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_1',A_8)
      | ~ v4_relat_1('#skF_4',A_8)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1176,c_16])).

tff(c_1262,plain,(
    ! [A_173] :
      ( r1_tarski('#skF_1',A_173)
      | ~ v4_relat_1('#skF_4',A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1223])).

tff(c_1266,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_246,c_1262])).

tff(c_458,plain,(
    ! [A_102,B_103,C_104] :
      ( k2_relset_1(A_102,B_103,C_104) = k2_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_467,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_458])).

tff(c_468,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_56])).

tff(c_1058,plain,(
    ! [C_157,A_158,B_159] :
      ( m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ r1_tarski(k2_relat_1(C_157),B_159)
      | ~ r1_tarski(k1_relat_1(C_157),A_158)
      | ~ v1_relat_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1665,plain,(
    ! [C_193,A_194,B_195] :
      ( r1_tarski(C_193,k2_zfmisc_1(A_194,B_195))
      | ~ r1_tarski(k2_relat_1(C_193),B_195)
      | ~ r1_tarski(k1_relat_1(C_193),A_194)
      | ~ v1_relat_1(C_193) ) ),
    inference(resolution,[status(thm)],[c_1058,c_10])).

tff(c_1667,plain,(
    ! [A_194] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_194,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_194)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_468,c_1665])).

tff(c_1671,plain,(
    ! [A_196] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_196,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1176,c_1667])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_401,plain,(
    ! [A_91,B_92,A_6] :
      ( k1_relset_1(A_91,B_92,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_91,B_92)) ) ),
    inference(resolution,[status(thm)],[c_12,c_393])).

tff(c_1688,plain,(
    ! [A_196] :
      ( k1_relset_1(A_196,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_196) ) ),
    inference(resolution,[status(thm)],[c_1671,c_401])).

tff(c_1726,plain,(
    ! [A_200] :
      ( k1_relset_1(A_200,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_1688])).

tff(c_1730,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1266,c_1726])).

tff(c_363,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_partfun1(C_86,A_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_372,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_363])).

tff(c_373,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_18,plain,(
    ! [A_10] :
      ( v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1229,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1176,c_18])).

tff(c_1256,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_1229])).

tff(c_26,plain,(
    ! [C_20,B_18,A_17] :
      ( v1_xboole_0(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(B_18,A_17)))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1335,plain,(
    ! [C_180,B_181,A_182] :
      ( v1_xboole_0(C_180)
      | ~ v1_xboole_0(B_181)
      | ~ r1_tarski(k2_relat_1(C_180),B_181)
      | ~ r1_tarski(k1_relat_1(C_180),A_182)
      | ~ v1_relat_1(C_180) ) ),
    inference(resolution,[status(thm)],[c_1058,c_26])).

tff(c_1337,plain,(
    ! [A_182] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_182)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_468,c_1335])).

tff(c_1340,plain,(
    ! [A_182] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0('#skF_3')
      | ~ r1_tarski('#skF_1',A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1176,c_1337])).

tff(c_1341,plain,(
    ! [A_182] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r1_tarski('#skF_1',A_182) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1256,c_1340])).

tff(c_1342,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1341])).

tff(c_1670,plain,(
    ! [A_194] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_194,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_1176,c_1667])).

tff(c_1827,plain,(
    ! [B_209,A_210,A_211] :
      ( k1_xboole_0 = B_209
      | k1_relset_1(A_210,B_209,A_211) = A_210
      | ~ v1_funct_2(A_211,A_210,B_209)
      | ~ r1_tarski(A_211,k2_zfmisc_1(A_210,B_209)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1160])).

tff(c_1842,plain,(
    ! [A_194] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1(A_194,'#skF_3','#skF_4') = A_194
      | ~ v1_funct_2('#skF_4',A_194,'#skF_3')
      | ~ r1_tarski('#skF_1',A_194) ) ),
    inference(resolution,[status(thm)],[c_1670,c_1827])).

tff(c_1861,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1842])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    ! [B_50,A_51] :
      ( ~ r1_xboole_0(B_50,A_51)
      | ~ r1_tarski(B_50,A_51)
      | v1_xboole_0(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,(
    ! [A_52] :
      ( ~ r1_tarski(A_52,k1_xboole_0)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_117,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_1894,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_117])).

tff(c_1903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1342,c_1894])).

tff(c_1905,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1842])).

tff(c_1317,plain,(
    ! [B_175,C_176,A_177] :
      ( k1_xboole_0 = B_175
      | v1_funct_2(C_176,A_177,B_175)
      | k1_relset_1(A_177,B_175,C_176) != A_177
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2225,plain,(
    ! [B_231,A_232,A_233] :
      ( k1_xboole_0 = B_231
      | v1_funct_2(A_232,A_233,B_231)
      | k1_relset_1(A_233,B_231,A_232) != A_233
      | ~ r1_tarski(A_232,k2_zfmisc_1(A_233,B_231)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1317])).

tff(c_2228,plain,(
    ! [A_194] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_194,'#skF_3')
      | k1_relset_1(A_194,'#skF_3','#skF_4') != A_194
      | ~ r1_tarski('#skF_1',A_194) ) ),
    inference(resolution,[status(thm)],[c_1670,c_2225])).

tff(c_2256,plain,(
    ! [A_236] :
      ( v1_funct_2('#skF_4',A_236,'#skF_3')
      | k1_relset_1(A_236,'#skF_3','#skF_4') != A_236
      | ~ r1_tarski('#skF_1',A_236) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1905,c_2228])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52])).

tff(c_141,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2262,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2256,c_141])).

tff(c_2267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_1730,c_2262])).

tff(c_2268,plain,(
    ! [A_182] : ~ r1_tarski('#skF_1',A_182) ),
    inference(splitRight,[status(thm)],[c_1341])).

tff(c_2327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2268,c_1266])).

tff(c_2329,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2337,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2329,c_2])).

tff(c_164,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v4_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_111,plain,(
    ! [A_3] :
      ( ~ r1_tarski(A_3,k1_xboole_0)
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_183,plain,(
    ! [B_61] :
      ( v1_xboole_0(k1_relat_1(B_61))
      | ~ v4_relat_1(B_61,k1_xboole_0)
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_164,c_111])).

tff(c_197,plain,(
    ! [B_61] :
      ( k1_relat_1(B_61) = k1_xboole_0
      | ~ v4_relat_1(B_61,k1_xboole_0)
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_2534,plain,(
    ! [B_256] :
      ( k1_relat_1(B_256) = '#skF_1'
      | ~ v4_relat_1(B_256,'#skF_1')
      | ~ v1_relat_1(B_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_2337,c_197])).

tff(c_2541,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_246,c_2534])).

tff(c_2547,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2541])).

tff(c_2351,plain,(
    ! [A_2] : r1_tarski('#skF_1',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_4])).

tff(c_2428,plain,(
    ! [A_246,B_247,C_248] :
      ( k2_relset_1(A_246,B_247,C_248) = k2_relat_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2437,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2428])).

tff(c_2460,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_56])).

tff(c_2939,plain,(
    ! [C_299,A_300,B_301] :
      ( m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301)))
      | ~ r1_tarski(k2_relat_1(C_299),B_301)
      | ~ r1_tarski(k1_relat_1(C_299),A_300)
      | ~ v1_relat_1(C_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3866,plain,(
    ! [C_347,A_348,B_349] :
      ( r1_tarski(C_347,k2_zfmisc_1(A_348,B_349))
      | ~ r1_tarski(k2_relat_1(C_347),B_349)
      | ~ r1_tarski(k1_relat_1(C_347),A_348)
      | ~ v1_relat_1(C_347) ) ),
    inference(resolution,[status(thm)],[c_2939,c_10])).

tff(c_3868,plain,(
    ! [A_348] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_348,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_348)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2460,c_3866])).

tff(c_3872,plain,(
    ! [A_350] : r1_tarski('#skF_4',k2_zfmisc_1(A_350,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2351,c_2547,c_3868])).

tff(c_2502,plain,(
    ! [A_252,B_253,C_254] :
      ( k1_relset_1(A_252,B_253,C_254) = k1_relat_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2510,plain,(
    ! [A_252,B_253,A_6] :
      ( k1_relset_1(A_252,B_253,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_252,B_253)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2502])).

tff(c_3886,plain,(
    ! [A_350] : k1_relset_1(A_350,'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3872,c_2510])).

tff(c_3913,plain,(
    ! [A_350] : k1_relset_1(A_350,'#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2547,c_3886])).

tff(c_44,plain,(
    ! [C_39,B_38] :
      ( v1_funct_2(C_39,k1_xboole_0,B_38)
      | k1_relset_1(k1_xboole_0,B_38,C_39) != k1_xboole_0
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2818,plain,(
    ! [C_286,B_287] :
      ( v1_funct_2(C_286,'#skF_1',B_287)
      | k1_relset_1('#skF_1',B_287,C_286) != '#skF_1'
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_287))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2337,c_2337,c_2337,c_2337,c_44])).

tff(c_2826,plain,(
    ! [A_6,B_287] :
      ( v1_funct_2(A_6,'#skF_1',B_287)
      | k1_relset_1('#skF_1',B_287,A_6) != '#skF_1'
      | ~ r1_tarski(A_6,k2_zfmisc_1('#skF_1',B_287)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2818])).

tff(c_3880,plain,
    ( v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_3872,c_2826])).

tff(c_3908,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_3880])).

tff(c_3926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3913,c_3908])).

tff(c_3927,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4846,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4807,c_3927])).

tff(c_4863,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3943,c_4195,c_4846])).

tff(c_4867,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_4863])).

tff(c_4871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3943,c_4055,c_4867])).

tff(c_4872,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4874,plain,(
    ! [A_2] : r1_tarski('#skF_1',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4872,c_4])).

tff(c_4875,plain,(
    ! [A_3] : r1_xboole_0(A_3,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4872,c_6])).

tff(c_4930,plain,(
    ! [B_465,A_466] :
      ( ~ r1_xboole_0(B_465,A_466)
      | ~ r1_tarski(B_465,A_466)
      | v1_xboole_0(B_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4935,plain,(
    ! [A_467] :
      ( ~ r1_tarski(A_467,'#skF_1')
      | v1_xboole_0(A_467) ) ),
    inference(resolution,[status(thm)],[c_4875,c_4930])).

tff(c_4940,plain,(
    v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4874,c_4935])).

tff(c_4873,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4880,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4872,c_4873])).

tff(c_4901,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4880,c_58])).

tff(c_6350,plain,(
    ! [C_620,B_621,A_622] :
      ( v1_xboole_0(C_620)
      | ~ m1_subset_1(C_620,k1_zfmisc_1(k2_zfmisc_1(B_621,A_622)))
      | ~ v1_xboole_0(A_622) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6357,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4901,c_6350])).

tff(c_6361,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4940,c_6357])).

tff(c_4888,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4872,c_2])).

tff(c_6369,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6361,c_4888])).

tff(c_6389,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6369,c_4874])).

tff(c_5112,plain,(
    ! [C_488,B_489,A_490] :
      ( v1_xboole_0(C_488)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(B_489,A_490)))
      | ~ v1_xboole_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5119,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4901,c_5112])).

tff(c_5123,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4940,c_5119])).

tff(c_5132,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5123,c_4888])).

tff(c_5145,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5132,c_5132,c_4901])).

tff(c_38,plain,(
    ! [C_36,A_33,B_34] :
      ( v1_partfun1(C_36,A_33)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5286,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5145,c_38])).

tff(c_5305,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5123,c_5286])).

tff(c_5151,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5132,c_4874])).

tff(c_5589,plain,(
    ! [C_540,A_541,B_542] :
      ( v1_funct_2(C_540,A_541,B_542)
      | ~ v1_partfun1(C_540,A_541)
      | ~ v1_funct_1(C_540)
      | ~ m1_subset_1(C_540,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6209,plain,(
    ! [A_591,A_592,B_593] :
      ( v1_funct_2(A_591,A_592,B_593)
      | ~ v1_partfun1(A_591,A_592)
      | ~ v1_funct_1(A_591)
      | ~ r1_tarski(A_591,k2_zfmisc_1(A_592,B_593)) ) ),
    inference(resolution,[status(thm)],[c_12,c_5589])).

tff(c_6213,plain,(
    ! [A_592,B_593] :
      ( v1_funct_2('#skF_4',A_592,B_593)
      | ~ v1_partfun1('#skF_4',A_592)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5151,c_6209])).

tff(c_6222,plain,(
    ! [A_594,B_595] :
      ( v1_funct_2('#skF_4',A_594,B_595)
      | ~ v1_partfun1('#skF_4',A_594) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6213])).

tff(c_4964,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_5139,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5132,c_4964])).

tff(c_6225,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_6222,c_5139])).

tff(c_6229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5305,c_6225])).

tff(c_6230,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_6235,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_6230])).

tff(c_6375,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6369,c_6235])).

tff(c_6500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6389,c_6375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 16:48:19 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.34/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.27  
% 6.34/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.27  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.34/2.27  
% 6.34/2.27  %Foreground sorts:
% 6.34/2.27  
% 6.34/2.27  
% 6.34/2.27  %Background operators:
% 6.34/2.27  
% 6.34/2.27  
% 6.34/2.27  %Foreground operators:
% 6.34/2.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.34/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.34/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.34/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.34/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.34/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.34/2.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.34/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.34/2.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.34/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.34/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.34/2.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.34/2.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.34/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.34/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.34/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.34/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.34/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.34/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.34/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.34/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.34/2.27  
% 6.61/2.30  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 6.61/2.30  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.61/2.30  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.61/2.30  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 6.61/2.30  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.61/2.30  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.61/2.30  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.61/2.30  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.61/2.30  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.61/2.30  tff(f_105, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 6.61/2.30  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 6.61/2.30  tff(f_72, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 6.61/2.30  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.61/2.30  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.61/2.30  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 6.61/2.30  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.61/2.30  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 6.61/2.30  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.61/2.30  tff(c_3934, plain, (![C_352, A_353, B_354]: (v1_relat_1(C_352) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.61/2.30  tff(c_3943, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3934])).
% 6.61/2.30  tff(c_4046, plain, (![C_372, A_373, B_374]: (v4_relat_1(C_372, A_373) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.61/2.30  tff(c_4055, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_4046])).
% 6.61/2.30  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.61/2.30  tff(c_4185, plain, (![A_390, B_391, C_392]: (k2_relset_1(A_390, B_391, C_392)=k2_relat_1(C_392) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.61/2.30  tff(c_4194, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_4185])).
% 6.61/2.30  tff(c_56, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.61/2.30  tff(c_4195, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4194, c_56])).
% 6.61/2.30  tff(c_4807, plain, (![C_452, A_453, B_454]: (m1_subset_1(C_452, k1_zfmisc_1(k2_zfmisc_1(A_453, B_454))) | ~r1_tarski(k2_relat_1(C_452), B_454) | ~r1_tarski(k1_relat_1(C_452), A_453) | ~v1_relat_1(C_452))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.61/2.30  tff(c_143, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.61/2.30  tff(c_152, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_143])).
% 6.61/2.30  tff(c_237, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.61/2.30  tff(c_246, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_237])).
% 6.61/2.30  tff(c_54, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.61/2.30  tff(c_67, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 6.61/2.30  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.61/2.30  tff(c_393, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.61/2.30  tff(c_402, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_393])).
% 6.61/2.30  tff(c_1160, plain, (![B_170, A_171, C_172]: (k1_xboole_0=B_170 | k1_relset_1(A_171, B_170, C_172)=A_171 | ~v1_funct_2(C_172, A_171, B_170) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_171, B_170))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.61/2.30  tff(c_1170, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_1160])).
% 6.61/2.30  tff(c_1175, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_402, c_1170])).
% 6.61/2.30  tff(c_1176, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_67, c_1175])).
% 6.61/2.30  tff(c_1223, plain, (![A_8]: (r1_tarski('#skF_1', A_8) | ~v4_relat_1('#skF_4', A_8) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1176, c_16])).
% 6.61/2.30  tff(c_1262, plain, (![A_173]: (r1_tarski('#skF_1', A_173) | ~v4_relat_1('#skF_4', A_173))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1223])).
% 6.61/2.30  tff(c_1266, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_246, c_1262])).
% 6.61/2.30  tff(c_458, plain, (![A_102, B_103, C_104]: (k2_relset_1(A_102, B_103, C_104)=k2_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.61/2.30  tff(c_467, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_458])).
% 6.61/2.30  tff(c_468, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_56])).
% 6.61/2.30  tff(c_1058, plain, (![C_157, A_158, B_159]: (m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~r1_tarski(k2_relat_1(C_157), B_159) | ~r1_tarski(k1_relat_1(C_157), A_158) | ~v1_relat_1(C_157))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.61/2.30  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.61/2.30  tff(c_1665, plain, (![C_193, A_194, B_195]: (r1_tarski(C_193, k2_zfmisc_1(A_194, B_195)) | ~r1_tarski(k2_relat_1(C_193), B_195) | ~r1_tarski(k1_relat_1(C_193), A_194) | ~v1_relat_1(C_193))), inference(resolution, [status(thm)], [c_1058, c_10])).
% 6.61/2.30  tff(c_1667, plain, (![A_194]: (r1_tarski('#skF_4', k2_zfmisc_1(A_194, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_194) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_468, c_1665])).
% 6.61/2.30  tff(c_1671, plain, (![A_196]: (r1_tarski('#skF_4', k2_zfmisc_1(A_196, '#skF_3')) | ~r1_tarski('#skF_1', A_196))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1176, c_1667])).
% 6.61/2.30  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.61/2.30  tff(c_401, plain, (![A_91, B_92, A_6]: (k1_relset_1(A_91, B_92, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_91, B_92)))), inference(resolution, [status(thm)], [c_12, c_393])).
% 6.61/2.30  tff(c_1688, plain, (![A_196]: (k1_relset_1(A_196, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_196))), inference(resolution, [status(thm)], [c_1671, c_401])).
% 6.61/2.30  tff(c_1726, plain, (![A_200]: (k1_relset_1(A_200, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_200))), inference(demodulation, [status(thm), theory('equality')], [c_1176, c_1688])).
% 6.61/2.30  tff(c_1730, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_1266, c_1726])).
% 6.61/2.30  tff(c_363, plain, (![C_86, A_87, B_88]: (v1_partfun1(C_86, A_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.61/2.30  tff(c_372, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_363])).
% 6.61/2.30  tff(c_373, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_372])).
% 6.61/2.30  tff(c_18, plain, (![A_10]: (v1_xboole_0(k1_relat_1(A_10)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.61/2.30  tff(c_1229, plain, (v1_xboole_0('#skF_1') | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1176, c_18])).
% 6.61/2.30  tff(c_1256, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_373, c_1229])).
% 6.61/2.30  tff(c_26, plain, (![C_20, B_18, A_17]: (v1_xboole_0(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(B_18, A_17))) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.61/2.30  tff(c_1335, plain, (![C_180, B_181, A_182]: (v1_xboole_0(C_180) | ~v1_xboole_0(B_181) | ~r1_tarski(k2_relat_1(C_180), B_181) | ~r1_tarski(k1_relat_1(C_180), A_182) | ~v1_relat_1(C_180))), inference(resolution, [status(thm)], [c_1058, c_26])).
% 6.61/2.30  tff(c_1337, plain, (![A_182]: (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), A_182) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_468, c_1335])).
% 6.61/2.30  tff(c_1340, plain, (![A_182]: (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3') | ~r1_tarski('#skF_1', A_182))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1176, c_1337])).
% 6.61/2.30  tff(c_1341, plain, (![A_182]: (~v1_xboole_0('#skF_3') | ~r1_tarski('#skF_1', A_182))), inference(negUnitSimplification, [status(thm)], [c_1256, c_1340])).
% 6.61/2.30  tff(c_1342, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1341])).
% 6.61/2.30  tff(c_1670, plain, (![A_194]: (r1_tarski('#skF_4', k2_zfmisc_1(A_194, '#skF_3')) | ~r1_tarski('#skF_1', A_194))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_1176, c_1667])).
% 6.61/2.30  tff(c_1827, plain, (![B_209, A_210, A_211]: (k1_xboole_0=B_209 | k1_relset_1(A_210, B_209, A_211)=A_210 | ~v1_funct_2(A_211, A_210, B_209) | ~r1_tarski(A_211, k2_zfmisc_1(A_210, B_209)))), inference(resolution, [status(thm)], [c_12, c_1160])).
% 6.61/2.30  tff(c_1842, plain, (![A_194]: (k1_xboole_0='#skF_3' | k1_relset_1(A_194, '#skF_3', '#skF_4')=A_194 | ~v1_funct_2('#skF_4', A_194, '#skF_3') | ~r1_tarski('#skF_1', A_194))), inference(resolution, [status(thm)], [c_1670, c_1827])).
% 6.61/2.30  tff(c_1861, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1842])).
% 6.61/2.30  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.61/2.30  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.61/2.30  tff(c_107, plain, (![B_50, A_51]: (~r1_xboole_0(B_50, A_51) | ~r1_tarski(B_50, A_51) | v1_xboole_0(B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.61/2.30  tff(c_112, plain, (![A_52]: (~r1_tarski(A_52, k1_xboole_0) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_6, c_107])).
% 6.61/2.30  tff(c_117, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_112])).
% 6.61/2.30  tff(c_1894, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1861, c_117])).
% 6.61/2.30  tff(c_1903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1342, c_1894])).
% 6.61/2.30  tff(c_1905, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1842])).
% 6.61/2.30  tff(c_1317, plain, (![B_175, C_176, A_177]: (k1_xboole_0=B_175 | v1_funct_2(C_176, A_177, B_175) | k1_relset_1(A_177, B_175, C_176)!=A_177 | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_175))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.61/2.30  tff(c_2225, plain, (![B_231, A_232, A_233]: (k1_xboole_0=B_231 | v1_funct_2(A_232, A_233, B_231) | k1_relset_1(A_233, B_231, A_232)!=A_233 | ~r1_tarski(A_232, k2_zfmisc_1(A_233, B_231)))), inference(resolution, [status(thm)], [c_12, c_1317])).
% 6.61/2.30  tff(c_2228, plain, (![A_194]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_194, '#skF_3') | k1_relset_1(A_194, '#skF_3', '#skF_4')!=A_194 | ~r1_tarski('#skF_1', A_194))), inference(resolution, [status(thm)], [c_1670, c_2225])).
% 6.61/2.30  tff(c_2256, plain, (![A_236]: (v1_funct_2('#skF_4', A_236, '#skF_3') | k1_relset_1(A_236, '#skF_3', '#skF_4')!=A_236 | ~r1_tarski('#skF_1', A_236))), inference(negUnitSimplification, [status(thm)], [c_1905, c_2228])).
% 6.61/2.30  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.61/2.30  tff(c_52, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.61/2.30  tff(c_64, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52])).
% 6.61/2.30  tff(c_141, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 6.61/2.30  tff(c_2262, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2256, c_141])).
% 6.61/2.30  tff(c_2267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1266, c_1730, c_2262])).
% 6.61/2.30  tff(c_2268, plain, (![A_182]: (~r1_tarski('#skF_1', A_182))), inference(splitRight, [status(thm)], [c_1341])).
% 6.61/2.30  tff(c_2327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2268, c_1266])).
% 6.61/2.30  tff(c_2329, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_372])).
% 6.61/2.30  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.61/2.30  tff(c_2337, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_2329, c_2])).
% 6.61/2.30  tff(c_164, plain, (![B_59, A_60]: (r1_tarski(k1_relat_1(B_59), A_60) | ~v4_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.61/2.30  tff(c_111, plain, (![A_3]: (~r1_tarski(A_3, k1_xboole_0) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_107])).
% 6.61/2.30  tff(c_183, plain, (![B_61]: (v1_xboole_0(k1_relat_1(B_61)) | ~v4_relat_1(B_61, k1_xboole_0) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_164, c_111])).
% 6.61/2.30  tff(c_197, plain, (![B_61]: (k1_relat_1(B_61)=k1_xboole_0 | ~v4_relat_1(B_61, k1_xboole_0) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_183, c_2])).
% 6.61/2.30  tff(c_2534, plain, (![B_256]: (k1_relat_1(B_256)='#skF_1' | ~v4_relat_1(B_256, '#skF_1') | ~v1_relat_1(B_256))), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_2337, c_197])).
% 6.61/2.30  tff(c_2541, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_246, c_2534])).
% 6.61/2.30  tff(c_2547, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2541])).
% 6.61/2.30  tff(c_2351, plain, (![A_2]: (r1_tarski('#skF_1', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_4])).
% 6.61/2.30  tff(c_2428, plain, (![A_246, B_247, C_248]: (k2_relset_1(A_246, B_247, C_248)=k2_relat_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.61/2.30  tff(c_2437, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2428])).
% 6.61/2.30  tff(c_2460, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_56])).
% 6.61/2.30  tff(c_2939, plain, (![C_299, A_300, B_301]: (m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))) | ~r1_tarski(k2_relat_1(C_299), B_301) | ~r1_tarski(k1_relat_1(C_299), A_300) | ~v1_relat_1(C_299))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.61/2.30  tff(c_3866, plain, (![C_347, A_348, B_349]: (r1_tarski(C_347, k2_zfmisc_1(A_348, B_349)) | ~r1_tarski(k2_relat_1(C_347), B_349) | ~r1_tarski(k1_relat_1(C_347), A_348) | ~v1_relat_1(C_347))), inference(resolution, [status(thm)], [c_2939, c_10])).
% 6.61/2.30  tff(c_3868, plain, (![A_348]: (r1_tarski('#skF_4', k2_zfmisc_1(A_348, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_348) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2460, c_3866])).
% 6.61/2.30  tff(c_3872, plain, (![A_350]: (r1_tarski('#skF_4', k2_zfmisc_1(A_350, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2351, c_2547, c_3868])).
% 6.61/2.30  tff(c_2502, plain, (![A_252, B_253, C_254]: (k1_relset_1(A_252, B_253, C_254)=k1_relat_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.61/2.30  tff(c_2510, plain, (![A_252, B_253, A_6]: (k1_relset_1(A_252, B_253, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_252, B_253)))), inference(resolution, [status(thm)], [c_12, c_2502])).
% 6.61/2.30  tff(c_3886, plain, (![A_350]: (k1_relset_1(A_350, '#skF_3', '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3872, c_2510])).
% 6.61/2.30  tff(c_3913, plain, (![A_350]: (k1_relset_1(A_350, '#skF_3', '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2547, c_3886])).
% 6.61/2.30  tff(c_44, plain, (![C_39, B_38]: (v1_funct_2(C_39, k1_xboole_0, B_38) | k1_relset_1(k1_xboole_0, B_38, C_39)!=k1_xboole_0 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_38))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.61/2.30  tff(c_2818, plain, (![C_286, B_287]: (v1_funct_2(C_286, '#skF_1', B_287) | k1_relset_1('#skF_1', B_287, C_286)!='#skF_1' | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_287))))), inference(demodulation, [status(thm), theory('equality')], [c_2337, c_2337, c_2337, c_2337, c_44])).
% 6.61/2.30  tff(c_2826, plain, (![A_6, B_287]: (v1_funct_2(A_6, '#skF_1', B_287) | k1_relset_1('#skF_1', B_287, A_6)!='#skF_1' | ~r1_tarski(A_6, k2_zfmisc_1('#skF_1', B_287)))), inference(resolution, [status(thm)], [c_12, c_2818])).
% 6.61/2.30  tff(c_3880, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_3872, c_2826])).
% 6.61/2.30  tff(c_3908, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_141, c_3880])).
% 6.61/2.30  tff(c_3926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3913, c_3908])).
% 6.61/2.30  tff(c_3927, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_64])).
% 6.61/2.30  tff(c_4846, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4807, c_3927])).
% 6.61/2.30  tff(c_4863, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3943, c_4195, c_4846])).
% 6.61/2.30  tff(c_4867, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_4863])).
% 6.61/2.30  tff(c_4871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3943, c_4055, c_4867])).
% 6.61/2.30  tff(c_4872, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_54])).
% 6.61/2.30  tff(c_4874, plain, (![A_2]: (r1_tarski('#skF_1', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_4872, c_4])).
% 6.61/2.30  tff(c_4875, plain, (![A_3]: (r1_xboole_0(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4872, c_6])).
% 6.61/2.30  tff(c_4930, plain, (![B_465, A_466]: (~r1_xboole_0(B_465, A_466) | ~r1_tarski(B_465, A_466) | v1_xboole_0(B_465))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.61/2.30  tff(c_4935, plain, (![A_467]: (~r1_tarski(A_467, '#skF_1') | v1_xboole_0(A_467))), inference(resolution, [status(thm)], [c_4875, c_4930])).
% 6.61/2.30  tff(c_4940, plain, (v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_4874, c_4935])).
% 6.61/2.30  tff(c_4873, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 6.61/2.30  tff(c_4880, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4872, c_4873])).
% 6.61/2.30  tff(c_4901, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4880, c_58])).
% 6.61/2.30  tff(c_6350, plain, (![C_620, B_621, A_622]: (v1_xboole_0(C_620) | ~m1_subset_1(C_620, k1_zfmisc_1(k2_zfmisc_1(B_621, A_622))) | ~v1_xboole_0(A_622))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.61/2.30  tff(c_6357, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_4901, c_6350])).
% 6.61/2.30  tff(c_6361, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4940, c_6357])).
% 6.61/2.30  tff(c_4888, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_4872, c_2])).
% 6.61/2.30  tff(c_6369, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_6361, c_4888])).
% 6.61/2.30  tff(c_6389, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_6369, c_4874])).
% 6.61/2.30  tff(c_5112, plain, (![C_488, B_489, A_490]: (v1_xboole_0(C_488) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(B_489, A_490))) | ~v1_xboole_0(A_490))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.61/2.30  tff(c_5119, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_4901, c_5112])).
% 6.61/2.30  tff(c_5123, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4940, c_5119])).
% 6.61/2.30  tff(c_5132, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_5123, c_4888])).
% 6.61/2.30  tff(c_5145, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5132, c_5132, c_4901])).
% 6.61/2.30  tff(c_38, plain, (![C_36, A_33, B_34]: (v1_partfun1(C_36, A_33) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.61/2.30  tff(c_5286, plain, (v1_partfun1('#skF_4', '#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_5145, c_38])).
% 6.61/2.30  tff(c_5305, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5123, c_5286])).
% 6.61/2.30  tff(c_5151, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_5132, c_4874])).
% 6.61/2.30  tff(c_5589, plain, (![C_540, A_541, B_542]: (v1_funct_2(C_540, A_541, B_542) | ~v1_partfun1(C_540, A_541) | ~v1_funct_1(C_540) | ~m1_subset_1(C_540, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.61/2.30  tff(c_6209, plain, (![A_591, A_592, B_593]: (v1_funct_2(A_591, A_592, B_593) | ~v1_partfun1(A_591, A_592) | ~v1_funct_1(A_591) | ~r1_tarski(A_591, k2_zfmisc_1(A_592, B_593)))), inference(resolution, [status(thm)], [c_12, c_5589])).
% 6.61/2.30  tff(c_6213, plain, (![A_592, B_593]: (v1_funct_2('#skF_4', A_592, B_593) | ~v1_partfun1('#skF_4', A_592) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5151, c_6209])).
% 6.61/2.30  tff(c_6222, plain, (![A_594, B_595]: (v1_funct_2('#skF_4', A_594, B_595) | ~v1_partfun1('#skF_4', A_594))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6213])).
% 6.61/2.30  tff(c_4964, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 6.61/2.30  tff(c_5139, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5132, c_4964])).
% 6.61/2.30  tff(c_6225, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_6222, c_5139])).
% 6.61/2.30  tff(c_6229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5305, c_6225])).
% 6.61/2.30  tff(c_6230, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_64])).
% 6.61/2.30  tff(c_6235, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_6230])).
% 6.61/2.30  tff(c_6375, plain, (~r1_tarski('#skF_4', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6369, c_6235])).
% 6.61/2.30  tff(c_6500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6389, c_6375])).
% 6.61/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.61/2.30  
% 6.61/2.30  Inference rules
% 6.61/2.30  ----------------------
% 6.61/2.30  #Ref     : 0
% 6.61/2.30  #Sup     : 1330
% 6.61/2.30  #Fact    : 0
% 6.61/2.30  #Define  : 0
% 6.61/2.30  #Split   : 19
% 6.61/2.30  #Chain   : 0
% 6.61/2.30  #Close   : 0
% 6.61/2.30  
% 6.61/2.30  Ordering : KBO
% 6.61/2.30  
% 6.61/2.30  Simplification rules
% 6.61/2.30  ----------------------
% 6.61/2.30  #Subsume      : 257
% 6.61/2.30  #Demod        : 1690
% 6.61/2.30  #Tautology    : 810
% 6.61/2.30  #SimpNegUnit  : 69
% 6.61/2.30  #BackRed      : 171
% 6.61/2.30  
% 6.61/2.30  #Partial instantiations: 0
% 6.61/2.30  #Strategies tried      : 1
% 6.61/2.30  
% 6.61/2.30  Timing (in seconds)
% 6.61/2.30  ----------------------
% 6.61/2.31  Preprocessing        : 0.33
% 6.61/2.31  Parsing              : 0.18
% 6.61/2.31  CNF conversion       : 0.02
% 6.61/2.31  Main loop            : 1.17
% 6.61/2.31  Inferencing          : 0.40
% 6.61/2.31  Reduction            : 0.41
% 6.61/2.31  Demodulation         : 0.29
% 6.61/2.31  BG Simplification    : 0.05
% 6.61/2.31  Subsumption          : 0.22
% 6.61/2.31  Abstraction          : 0.05
% 6.61/2.31  MUC search           : 0.00
% 6.61/2.31  Cooper               : 0.00
% 6.61/2.31  Total                : 1.57
% 6.61/2.31  Index Insertion      : 0.00
% 6.61/2.31  Index Deletion       : 0.00
% 6.61/2.31  Index Matching       : 0.00
% 6.61/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
