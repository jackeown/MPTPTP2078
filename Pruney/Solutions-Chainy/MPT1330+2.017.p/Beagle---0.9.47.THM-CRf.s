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
% DateTime   : Thu Dec  3 10:23:11 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 917 expanded)
%              Number of leaves         :   45 ( 323 expanded)
%              Depth                    :   14
%              Number of atoms          :  257 (2409 expanded)
%              Number of equality atoms :   69 ( 902 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_22,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_97,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_105,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_97])).

tff(c_62,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_104,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_97])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_117,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_104,c_56])).

tff(c_127,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_130,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_117,c_127])).

tff(c_136,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_130])).

tff(c_247,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_255,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_117,c_247])).

tff(c_328,plain,(
    ! [B_100,A_101] :
      ( k1_relat_1(B_100) = A_101
      | ~ v1_partfun1(B_100,A_101)
      | ~ v4_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_331,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_328])).

tff(c_337,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_331])).

tff(c_342,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_54,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_86,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_58,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_110,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_58])).

tff(c_111,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_110])).

tff(c_605,plain,(
    ! [B_147,C_148,A_149] :
      ( k1_xboole_0 = B_147
      | v1_partfun1(C_148,A_149)
      | ~ v1_funct_2(C_148,A_149,B_147)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_147)))
      | ~ v1_funct_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_608,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_605])).

tff(c_615,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_111,c_608])).

tff(c_617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_86,c_615])).

tff(c_618,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_626,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_117])).

tff(c_839,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k8_relset_1(A_169,B_170,C_171,D_172) = k10_relat_1(C_171,D_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_845,plain,(
    ! [D_172] : k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',D_172) = k10_relat_1('#skF_3',D_172) ),
    inference(resolution,[status(thm)],[c_626,c_839])).

tff(c_52,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_160,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_104,c_52])).

tff(c_623,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_618,c_160])).

tff(c_847,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_623])).

tff(c_198,plain,(
    ! [C_75,B_76,A_77] :
      ( v5_relat_1(C_75,B_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_206,plain,(
    v5_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_117,c_198])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_664,plain,(
    ! [B_150,A_151] :
      ( k5_relat_1(B_150,k6_relat_1(A_151)) = B_150
      | ~ r1_tarski(k2_relat_1(B_150),A_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_671,plain,(
    ! [B_14,A_13] :
      ( k5_relat_1(B_14,k6_relat_1(A_13)) = B_14
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_664])).

tff(c_32,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_768,plain,(
    ! [A_160,B_161] :
      ( k10_relat_1(A_160,k1_relat_1(B_161)) = k1_relat_1(k5_relat_1(A_160,B_161))
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_777,plain,(
    ! [A_160,A_20] :
      ( k1_relat_1(k5_relat_1(A_160,k6_relat_1(A_20))) = k10_relat_1(A_160,A_20)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_768])).

tff(c_782,plain,(
    ! [A_162,A_163] :
      ( k1_relat_1(k5_relat_1(A_162,k6_relat_1(A_163))) = k10_relat_1(A_162,A_163)
      | ~ v1_relat_1(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_777])).

tff(c_885,plain,(
    ! [B_185,A_186] :
      ( k10_relat_1(B_185,A_186) = k1_relat_1(B_185)
      | ~ v1_relat_1(B_185)
      | ~ v5_relat_1(B_185,A_186)
      | ~ v1_relat_1(B_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_782])).

tff(c_888,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_206,c_885])).

tff(c_894,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_888])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_847,c_894])).

tff(c_897,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_917,plain,(
    ! [A_190] :
      ( u1_struct_0(A_190) = k2_struct_0(A_190)
      | ~ l1_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_923,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_917])).

tff(c_927,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_923])).

tff(c_898,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_920,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_917])).

tff(c_925,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_920])).

tff(c_949,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_925,c_56])).

tff(c_1552,plain,(
    ! [A_272,B_273,C_274,D_275] :
      ( k8_relset_1(A_272,B_273,C_274,D_275) = k10_relat_1(C_274,D_275)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1558,plain,(
    ! [D_275] : k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',D_275) = k10_relat_1('#skF_3',D_275) ),
    inference(resolution,[status(thm)],[c_949,c_1552])).

tff(c_989,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_925,c_898,c_897,c_52])).

tff(c_1560,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_989])).

tff(c_1069,plain,(
    ! [C_225,A_226,B_227] :
      ( v4_relat_1(C_225,A_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1077,plain,(
    v4_relat_1('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_949,c_1069])).

tff(c_964,plain,(
    ! [B_199,A_200] :
      ( v1_relat_1(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_200))
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_967,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_949,c_964])).

tff(c_973,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_967])).

tff(c_1208,plain,(
    ! [B_244,A_245] :
      ( k1_relat_1(B_244) = A_245
      | ~ v1_partfun1(B_244,A_245)
      | ~ v4_relat_1(B_244,A_245)
      | ~ v1_relat_1(B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1211,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1077,c_1208])).

tff(c_1217,plain,
    ( k1_relat_1('#skF_3') = k1_xboole_0
    | ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_1211])).

tff(c_1221,plain,(
    ~ v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1217])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1013,plain,(
    ! [B_217,A_218] :
      ( r1_tarski(k1_relat_1(B_217),A_218)
      | ~ v4_relat_1(B_217,A_218)
      | ~ v1_relat_1(B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_944,plain,(
    ! [B_195,A_196] :
      ( v1_xboole_0(B_195)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_196))
      | ~ v1_xboole_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_948,plain,(
    ! [A_6,B_7] :
      ( v1_xboole_0(A_6)
      | ~ v1_xboole_0(B_7)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_944])).

tff(c_1377,plain,(
    ! [B_261,A_262] :
      ( v1_xboole_0(k1_relat_1(B_261))
      | ~ v1_xboole_0(A_262)
      | ~ v4_relat_1(B_261,A_262)
      | ~ v1_relat_1(B_261) ) ),
    inference(resolution,[status(thm)],[c_1013,c_948])).

tff(c_1379,plain,
    ( v1_xboole_0(k1_relat_1('#skF_3'))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1077,c_1377])).

tff(c_1384,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_2,c_1379])).

tff(c_907,plain,(
    ! [B_187,A_188] :
      ( ~ v1_xboole_0(B_187)
      | B_187 = A_188
      | ~ v1_xboole_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_910,plain,(
    ! [A_188] :
      ( k1_xboole_0 = A_188
      | ~ v1_xboole_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_2,c_907])).

tff(c_1393,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1384,c_910])).

tff(c_42,plain,(
    ! [B_32] :
      ( v1_partfun1(B_32,k1_relat_1(B_32))
      | ~ v4_relat_1(B_32,k1_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1405,plain,
    ( v1_partfun1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v4_relat_1('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1393,c_42])).

tff(c_1417,plain,(
    v1_partfun1('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_1077,c_1393,c_1405])).

tff(c_1419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1221,c_1417])).

tff(c_1420,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1217])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1428,plain,(
    ! [A_11] :
      ( r1_tarski(k1_xboole_0,A_11)
      | ~ v4_relat_1('#skF_3',A_11)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_16])).

tff(c_1461,plain,(
    ! [A_265] :
      ( r1_tarski(k1_xboole_0,A_265)
      | ~ v4_relat_1('#skF_3',A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_1428])).

tff(c_1465,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1077,c_1461])).

tff(c_990,plain,(
    ! [C_207,B_208,A_209] :
      ( v5_relat_1(C_207,B_208)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_209,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_998,plain,(
    v5_relat_1('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_949,c_990])).

tff(c_1041,plain,(
    ! [B_221,A_222] :
      ( r1_tarski(k2_relat_1(B_221),A_222)
      | ~ v5_relat_1(B_221,A_222)
      | ~ v1_relat_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1168,plain,(
    ! [B_242,A_243] :
      ( v1_xboole_0(k2_relat_1(B_242))
      | ~ v1_xboole_0(A_243)
      | ~ v5_relat_1(B_242,A_243)
      | ~ v1_relat_1(B_242) ) ),
    inference(resolution,[status(thm)],[c_1041,c_948])).

tff(c_1172,plain,
    ( v1_xboole_0(k2_relat_1('#skF_3'))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_998,c_1168])).

tff(c_1178,plain,(
    v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_2,c_1172])).

tff(c_1184,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1178,c_910])).

tff(c_30,plain,(
    ! [B_22,A_21] :
      ( k5_relat_1(B_22,k6_relat_1(A_21)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1191,plain,(
    ! [A_21] :
      ( k5_relat_1('#skF_3',k6_relat_1(A_21)) = '#skF_3'
      | ~ r1_tarski(k1_xboole_0,A_21)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_30])).

tff(c_1201,plain,(
    ! [A_21] :
      ( k5_relat_1('#skF_3',k6_relat_1(A_21)) = '#skF_3'
      | ~ r1_tarski(k1_xboole_0,A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_1191])).

tff(c_1441,plain,(
    ! [A_263,B_264] :
      ( k10_relat_1(A_263,k1_relat_1(B_264)) = k1_relat_1(k5_relat_1(A_263,B_264))
      | ~ v1_relat_1(B_264)
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1453,plain,(
    ! [A_263,A_20] :
      ( k1_relat_1(k5_relat_1(A_263,k6_relat_1(A_20))) = k10_relat_1(A_263,A_20)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(A_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1441])).

tff(c_1597,plain,(
    ! [A_280,A_281] :
      ( k1_relat_1(k5_relat_1(A_280,k6_relat_1(A_281))) = k10_relat_1(A_280,A_281)
      | ~ v1_relat_1(A_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1453])).

tff(c_1618,plain,(
    ! [A_21] :
      ( k10_relat_1('#skF_3',A_21) = k1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(k1_xboole_0,A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1201,c_1597])).

tff(c_1631,plain,(
    ! [A_282] :
      ( k10_relat_1('#skF_3',A_282) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_1420,c_1618])).

tff(c_1634,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1465,c_1631])).

tff(c_1638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1560,c_1634])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.65  
% 3.57/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.57/1.65  
% 3.57/1.65  %Foreground sorts:
% 3.57/1.65  
% 3.57/1.65  
% 3.57/1.65  %Background operators:
% 3.57/1.65  
% 3.57/1.65  
% 3.57/1.65  %Foreground operators:
% 3.57/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.57/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.65  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.57/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.57/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.57/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.57/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.57/1.65  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.57/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.57/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.57/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.57/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.57/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.65  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.57/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.57/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.57/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.57/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.57/1.65  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.57/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.57/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.57/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.65  
% 3.57/1.68  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.57/1.68  tff(f_145, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 3.57/1.68  tff(f_126, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.57/1.68  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.57/1.68  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.57/1.68  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.57/1.68  tff(f_122, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 3.57/1.68  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.57/1.68  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.57/1.68  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.57/1.68  tff(f_87, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.57/1.68  tff(f_77, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.57/1.68  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.57/1.68  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.57/1.68  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.57/1.68  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.57/1.68  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.57/1.68  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.57/1.68  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.57/1.68  tff(c_64, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.57/1.68  tff(c_97, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.68  tff(c_105, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_97])).
% 3.57/1.68  tff(c_62, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.57/1.68  tff(c_104, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_97])).
% 3.57/1.68  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.57/1.68  tff(c_117, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_104, c_56])).
% 3.57/1.68  tff(c_127, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.68  tff(c_130, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_117, c_127])).
% 3.57/1.68  tff(c_136, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_130])).
% 3.57/1.68  tff(c_247, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.68  tff(c_255, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_117, c_247])).
% 3.57/1.68  tff(c_328, plain, (![B_100, A_101]: (k1_relat_1(B_100)=A_101 | ~v1_partfun1(B_100, A_101) | ~v4_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.57/1.68  tff(c_331, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_255, c_328])).
% 3.57/1.68  tff(c_337, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_331])).
% 3.57/1.68  tff(c_342, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_337])).
% 3.57/1.68  tff(c_54, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.57/1.68  tff(c_86, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.57/1.68  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.57/1.68  tff(c_58, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.57/1.68  tff(c_110, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_58])).
% 3.57/1.68  tff(c_111, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_110])).
% 3.57/1.68  tff(c_605, plain, (![B_147, C_148, A_149]: (k1_xboole_0=B_147 | v1_partfun1(C_148, A_149) | ~v1_funct_2(C_148, A_149, B_147) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_147))) | ~v1_funct_1(C_148))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.57/1.68  tff(c_608, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_117, c_605])).
% 3.57/1.68  tff(c_615, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_111, c_608])).
% 3.57/1.68  tff(c_617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_86, c_615])).
% 3.57/1.68  tff(c_618, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_337])).
% 3.57/1.68  tff(c_626, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_117])).
% 3.57/1.68  tff(c_839, plain, (![A_169, B_170, C_171, D_172]: (k8_relset_1(A_169, B_170, C_171, D_172)=k10_relat_1(C_171, D_172) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.57/1.68  tff(c_845, plain, (![D_172]: (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', D_172)=k10_relat_1('#skF_3', D_172))), inference(resolution, [status(thm)], [c_626, c_839])).
% 3.57/1.68  tff(c_52, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.57/1.68  tff(c_160, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_104, c_52])).
% 3.57/1.68  tff(c_623, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_618, c_618, c_160])).
% 3.57/1.68  tff(c_847, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_623])).
% 3.57/1.68  tff(c_198, plain, (![C_75, B_76, A_77]: (v5_relat_1(C_75, B_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.68  tff(c_206, plain, (v5_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_117, c_198])).
% 3.57/1.68  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.57/1.68  tff(c_664, plain, (![B_150, A_151]: (k5_relat_1(B_150, k6_relat_1(A_151))=B_150 | ~r1_tarski(k2_relat_1(B_150), A_151) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.57/1.68  tff(c_671, plain, (![B_14, A_13]: (k5_relat_1(B_14, k6_relat_1(A_13))=B_14 | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_20, c_664])).
% 3.57/1.68  tff(c_32, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.57/1.68  tff(c_26, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.57/1.68  tff(c_768, plain, (![A_160, B_161]: (k10_relat_1(A_160, k1_relat_1(B_161))=k1_relat_1(k5_relat_1(A_160, B_161)) | ~v1_relat_1(B_161) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.57/1.68  tff(c_777, plain, (![A_160, A_20]: (k1_relat_1(k5_relat_1(A_160, k6_relat_1(A_20)))=k10_relat_1(A_160, A_20) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(A_160))), inference(superposition, [status(thm), theory('equality')], [c_26, c_768])).
% 3.57/1.68  tff(c_782, plain, (![A_162, A_163]: (k1_relat_1(k5_relat_1(A_162, k6_relat_1(A_163)))=k10_relat_1(A_162, A_163) | ~v1_relat_1(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_777])).
% 3.57/1.68  tff(c_885, plain, (![B_185, A_186]: (k10_relat_1(B_185, A_186)=k1_relat_1(B_185) | ~v1_relat_1(B_185) | ~v5_relat_1(B_185, A_186) | ~v1_relat_1(B_185))), inference(superposition, [status(thm), theory('equality')], [c_671, c_782])).
% 3.57/1.68  tff(c_888, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_206, c_885])).
% 3.57/1.68  tff(c_894, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_888])).
% 3.57/1.68  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_847, c_894])).
% 3.57/1.68  tff(c_897, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.57/1.68  tff(c_917, plain, (![A_190]: (u1_struct_0(A_190)=k2_struct_0(A_190) | ~l1_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.57/1.68  tff(c_923, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_917])).
% 3.57/1.68  tff(c_927, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_897, c_923])).
% 3.57/1.68  tff(c_898, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.57/1.68  tff(c_920, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_917])).
% 3.57/1.68  tff(c_925, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_898, c_920])).
% 3.57/1.68  tff(c_949, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_927, c_925, c_56])).
% 3.57/1.68  tff(c_1552, plain, (![A_272, B_273, C_274, D_275]: (k8_relset_1(A_272, B_273, C_274, D_275)=k10_relat_1(C_274, D_275) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.57/1.68  tff(c_1558, plain, (![D_275]: (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', D_275)=k10_relat_1('#skF_3', D_275))), inference(resolution, [status(thm)], [c_949, c_1552])).
% 3.57/1.68  tff(c_989, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_927, c_925, c_898, c_897, c_52])).
% 3.57/1.68  tff(c_1560, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_989])).
% 3.57/1.68  tff(c_1069, plain, (![C_225, A_226, B_227]: (v4_relat_1(C_225, A_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.68  tff(c_1077, plain, (v4_relat_1('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_949, c_1069])).
% 3.57/1.68  tff(c_964, plain, (![B_199, A_200]: (v1_relat_1(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(A_200)) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.57/1.68  tff(c_967, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_949, c_964])).
% 3.57/1.68  tff(c_973, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_967])).
% 3.57/1.68  tff(c_1208, plain, (![B_244, A_245]: (k1_relat_1(B_244)=A_245 | ~v1_partfun1(B_244, A_245) | ~v4_relat_1(B_244, A_245) | ~v1_relat_1(B_244))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.57/1.68  tff(c_1211, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1077, c_1208])).
% 3.57/1.68  tff(c_1217, plain, (k1_relat_1('#skF_3')=k1_xboole_0 | ~v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_973, c_1211])).
% 3.57/1.68  tff(c_1221, plain, (~v1_partfun1('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1217])).
% 3.57/1.68  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.57/1.68  tff(c_1013, plain, (![B_217, A_218]: (r1_tarski(k1_relat_1(B_217), A_218) | ~v4_relat_1(B_217, A_218) | ~v1_relat_1(B_217))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.68  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.57/1.68  tff(c_944, plain, (![B_195, A_196]: (v1_xboole_0(B_195) | ~m1_subset_1(B_195, k1_zfmisc_1(A_196)) | ~v1_xboole_0(A_196))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.57/1.68  tff(c_948, plain, (![A_6, B_7]: (v1_xboole_0(A_6) | ~v1_xboole_0(B_7) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_944])).
% 3.57/1.68  tff(c_1377, plain, (![B_261, A_262]: (v1_xboole_0(k1_relat_1(B_261)) | ~v1_xboole_0(A_262) | ~v4_relat_1(B_261, A_262) | ~v1_relat_1(B_261))), inference(resolution, [status(thm)], [c_1013, c_948])).
% 3.57/1.68  tff(c_1379, plain, (v1_xboole_0(k1_relat_1('#skF_3')) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1077, c_1377])).
% 3.57/1.68  tff(c_1384, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_2, c_1379])).
% 3.57/1.68  tff(c_907, plain, (![B_187, A_188]: (~v1_xboole_0(B_187) | B_187=A_188 | ~v1_xboole_0(A_188))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.57/1.68  tff(c_910, plain, (![A_188]: (k1_xboole_0=A_188 | ~v1_xboole_0(A_188))), inference(resolution, [status(thm)], [c_2, c_907])).
% 3.57/1.68  tff(c_1393, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1384, c_910])).
% 3.57/1.68  tff(c_42, plain, (![B_32]: (v1_partfun1(B_32, k1_relat_1(B_32)) | ~v4_relat_1(B_32, k1_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.57/1.68  tff(c_1405, plain, (v1_partfun1('#skF_3', k1_relat_1('#skF_3')) | ~v4_relat_1('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1393, c_42])).
% 3.57/1.68  tff(c_1417, plain, (v1_partfun1('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_973, c_1077, c_1393, c_1405])).
% 3.57/1.68  tff(c_1419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1221, c_1417])).
% 3.57/1.68  tff(c_1420, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1217])).
% 3.57/1.68  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.57/1.68  tff(c_1428, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11) | ~v4_relat_1('#skF_3', A_11) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1420, c_16])).
% 3.57/1.68  tff(c_1461, plain, (![A_265]: (r1_tarski(k1_xboole_0, A_265) | ~v4_relat_1('#skF_3', A_265))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_1428])).
% 3.57/1.68  tff(c_1465, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_1077, c_1461])).
% 3.57/1.68  tff(c_990, plain, (![C_207, B_208, A_209]: (v5_relat_1(C_207, B_208) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_209, B_208))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.68  tff(c_998, plain, (v5_relat_1('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_949, c_990])).
% 3.57/1.68  tff(c_1041, plain, (![B_221, A_222]: (r1_tarski(k2_relat_1(B_221), A_222) | ~v5_relat_1(B_221, A_222) | ~v1_relat_1(B_221))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.57/1.68  tff(c_1168, plain, (![B_242, A_243]: (v1_xboole_0(k2_relat_1(B_242)) | ~v1_xboole_0(A_243) | ~v5_relat_1(B_242, A_243) | ~v1_relat_1(B_242))), inference(resolution, [status(thm)], [c_1041, c_948])).
% 3.57/1.68  tff(c_1172, plain, (v1_xboole_0(k2_relat_1('#skF_3')) | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_998, c_1168])).
% 3.57/1.68  tff(c_1178, plain, (v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_2, c_1172])).
% 3.57/1.68  tff(c_1184, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1178, c_910])).
% 3.57/1.68  tff(c_30, plain, (![B_22, A_21]: (k5_relat_1(B_22, k6_relat_1(A_21))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.57/1.68  tff(c_1191, plain, (![A_21]: (k5_relat_1('#skF_3', k6_relat_1(A_21))='#skF_3' | ~r1_tarski(k1_xboole_0, A_21) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1184, c_30])).
% 3.57/1.68  tff(c_1201, plain, (![A_21]: (k5_relat_1('#skF_3', k6_relat_1(A_21))='#skF_3' | ~r1_tarski(k1_xboole_0, A_21))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_1191])).
% 3.57/1.68  tff(c_1441, plain, (![A_263, B_264]: (k10_relat_1(A_263, k1_relat_1(B_264))=k1_relat_1(k5_relat_1(A_263, B_264)) | ~v1_relat_1(B_264) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.57/1.68  tff(c_1453, plain, (![A_263, A_20]: (k1_relat_1(k5_relat_1(A_263, k6_relat_1(A_20)))=k10_relat_1(A_263, A_20) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(A_263))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1441])).
% 3.57/1.68  tff(c_1597, plain, (![A_280, A_281]: (k1_relat_1(k5_relat_1(A_280, k6_relat_1(A_281)))=k10_relat_1(A_280, A_281) | ~v1_relat_1(A_280))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1453])).
% 3.57/1.68  tff(c_1618, plain, (![A_21]: (k10_relat_1('#skF_3', A_21)=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(k1_xboole_0, A_21))), inference(superposition, [status(thm), theory('equality')], [c_1201, c_1597])).
% 3.57/1.68  tff(c_1631, plain, (![A_282]: (k10_relat_1('#skF_3', A_282)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_282))), inference(demodulation, [status(thm), theory('equality')], [c_973, c_1420, c_1618])).
% 3.57/1.68  tff(c_1634, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1465, c_1631])).
% 3.57/1.68  tff(c_1638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1560, c_1634])).
% 3.57/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.68  
% 3.57/1.68  Inference rules
% 3.57/1.68  ----------------------
% 3.57/1.68  #Ref     : 0
% 3.57/1.68  #Sup     : 318
% 3.57/1.68  #Fact    : 0
% 3.57/1.68  #Define  : 0
% 3.57/1.68  #Split   : 11
% 3.57/1.68  #Chain   : 0
% 3.57/1.68  #Close   : 0
% 3.57/1.68  
% 3.57/1.68  Ordering : KBO
% 3.57/1.68  
% 3.57/1.68  Simplification rules
% 3.57/1.68  ----------------------
% 3.57/1.68  #Subsume      : 35
% 3.57/1.68  #Demod        : 223
% 3.57/1.68  #Tautology    : 134
% 3.57/1.68  #SimpNegUnit  : 11
% 3.57/1.68  #BackRed      : 19
% 3.57/1.68  
% 3.57/1.68  #Partial instantiations: 0
% 3.57/1.68  #Strategies tried      : 1
% 3.57/1.68  
% 3.57/1.68  Timing (in seconds)
% 3.57/1.68  ----------------------
% 3.57/1.68  Preprocessing        : 0.35
% 3.57/1.68  Parsing              : 0.19
% 3.57/1.68  CNF conversion       : 0.02
% 3.57/1.68  Main loop            : 0.48
% 3.57/1.68  Inferencing          : 0.18
% 3.57/1.68  Reduction            : 0.16
% 3.57/1.68  Demodulation         : 0.11
% 3.57/1.68  BG Simplification    : 0.02
% 3.57/1.68  Subsumption          : 0.07
% 3.57/1.68  Abstraction          : 0.02
% 3.57/1.68  MUC search           : 0.00
% 3.57/1.68  Cooper               : 0.00
% 3.57/1.68  Total                : 0.88
% 3.57/1.68  Index Insertion      : 0.00
% 3.57/1.68  Index Deletion       : 0.00
% 3.57/1.68  Index Matching       : 0.00
% 3.57/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
