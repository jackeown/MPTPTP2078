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
% DateTime   : Thu Dec  3 10:23:21 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 646 expanded)
%              Number of leaves         :   40 ( 258 expanded)
%              Depth                    :   10
%              Number of atoms          :  228 (2133 expanded)
%              Number of equality atoms :   92 ( 757 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_78,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_54,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_58,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_59,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_67,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_59])).

tff(c_66,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_59])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_66,c_48])).

tff(c_8,plain,(
    ! [C_7,A_5,B_6] :
      ( v1_relat_1(C_7)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_83,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_8])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_50,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_76,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_66,c_50])).

tff(c_108,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k8_relset_1(A_44,B_45,C_46,D_47) = k10_relat_1(C_46,D_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_111,plain,(
    ! [D_47] : k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_47) = k10_relat_1('#skF_3',D_47) ),
    inference(resolution,[status(thm)],[c_79,c_108])).

tff(c_386,plain,(
    ! [A_120,B_121,C_122] :
      ( k8_relset_1(A_120,B_121,C_122,B_121) = k1_relset_1(A_120,B_121,C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_388,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_386])).

tff(c_390,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k10_relat_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_388])).

tff(c_400,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_403,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_1')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_79,c_400])).

tff(c_406,plain,
    ( k2_struct_0('#skF_2') = k1_xboole_0
    | k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_390,c_403])).

tff(c_407,plain,(
    k10_relat_1('#skF_3',k2_struct_0('#skF_2')) = k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_406])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k9_relat_1(k2_funct_1(B_4),A_3) = k10_relat_1(B_4,A_3)
      | ~ v2_funct_1(B_4)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_84,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_66,c_46])).

tff(c_455,plain,(
    ! [C_140,B_141,A_142] :
      ( m1_subset_1(k2_funct_1(C_140),k1_zfmisc_1(k2_zfmisc_1(B_141,A_142)))
      | k2_relset_1(A_142,B_141,C_140) != B_141
      | ~ v2_funct_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_142,B_141)))
      | ~ v1_funct_2(C_140,A_142,B_141)
      | ~ v1_funct_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k7_relset_1(A_8,B_9,C_10,D_11) = k9_relat_1(C_10,D_11)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_518,plain,(
    ! [B_146,A_147,C_148,D_149] :
      ( k7_relset_1(B_146,A_147,k2_funct_1(C_148),D_149) = k9_relat_1(k2_funct_1(C_148),D_149)
      | k2_relset_1(A_147,B_146,C_148) != B_146
      | ~ v2_funct_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146)))
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ v1_funct_1(C_148) ) ),
    inference(resolution,[status(thm)],[c_455,c_10])).

tff(c_522,plain,(
    ! [D_149] :
      ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_149) = k9_relat_1(k2_funct_1('#skF_3'),D_149)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_79,c_518])).

tff(c_526,plain,(
    ! [D_149] : k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_149) = k9_relat_1(k2_funct_1('#skF_3'),D_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_44,c_84,c_522])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] :
      ( k7_relset_1(A_16,B_17,C_18,A_16) = k2_relset_1(A_16,B_17,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_583,plain,(
    ! [B_161,A_162,C_163] :
      ( k7_relset_1(B_161,A_162,k2_funct_1(C_163),B_161) = k2_relset_1(B_161,A_162,k2_funct_1(C_163))
      | k2_relset_1(A_162,B_161,C_163) != B_161
      | ~ v2_funct_1(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161)))
      | ~ v1_funct_2(C_163,A_162,B_161)
      | ~ v1_funct_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_455,c_16])).

tff(c_587,plain,
    ( k7_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) = k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_583])).

tff(c_591,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_44,c_84,c_526,c_587])).

tff(c_438,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_tops_2(A_137,B_138,C_139) = k2_funct_1(C_139)
      | ~ v2_funct_1(C_139)
      | k2_relset_1(A_137,B_138,C_139) != B_138
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_2(C_139,A_137,B_138)
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_441,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_438])).

tff(c_444,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_84,c_44,c_441])).

tff(c_123,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( k7_relset_1(A_49,B_50,C_51,D_52) = k9_relat_1(C_51,D_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_126,plain,(
    ! [D_52] : k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',D_52) = k9_relat_1('#skF_3',D_52) ),
    inference(resolution,[status(thm)],[c_79,c_123])).

tff(c_137,plain,(
    ! [A_56,B_57,C_58] :
      ( k7_relset_1(A_56,B_57,C_58,A_56) = k2_relset_1(A_56,B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_139,plain,(
    k7_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_1')) = k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_137])).

tff(c_141,plain,(
    k9_relat_1('#skF_3',k2_struct_0('#skF_1')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_84,c_139])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( k10_relat_1(k2_funct_1(B_2),A_1) = k9_relat_1(B_2,A_1)
      | ~ v2_funct_1(B_2)
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_207,plain,(
    ! [C_81,B_82,A_83] :
      ( m1_subset_1(k2_funct_1(C_81),k1_zfmisc_1(k2_zfmisc_1(B_82,A_83)))
      | k2_relset_1(A_83,B_82,C_81) != B_82
      | ~ v2_funct_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82)))
      | ~ v1_funct_2(C_81,A_83,B_82)
      | ~ v1_funct_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( k8_relset_1(A_12,B_13,C_14,D_15) = k10_relat_1(C_14,D_15)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_276,plain,(
    ! [B_89,A_90,C_91,D_92] :
      ( k8_relset_1(B_89,A_90,k2_funct_1(C_91),D_92) = k10_relat_1(k2_funct_1(C_91),D_92)
      | k2_relset_1(A_90,B_89,C_91) != B_89
      | ~ v2_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89)))
      | ~ v1_funct_2(C_91,A_90,B_89)
      | ~ v1_funct_1(C_91) ) ),
    inference(resolution,[status(thm)],[c_207,c_12])).

tff(c_280,plain,(
    ! [D_92] :
      ( k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_92) = k10_relat_1(k2_funct_1('#skF_3'),D_92)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_79,c_276])).

tff(c_284,plain,(
    ! [D_92] : k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),D_92) = k10_relat_1(k2_funct_1('#skF_3'),D_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_44,c_84,c_280])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18] :
      ( k8_relset_1(A_16,B_17,C_18,B_17) = k1_relset_1(A_16,B_17,C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_325,plain,(
    ! [B_102,A_103,C_104] :
      ( k8_relset_1(B_102,A_103,k2_funct_1(C_104),A_103) = k1_relset_1(B_102,A_103,k2_funct_1(C_104))
      | k2_relset_1(A_103,B_102,C_104) != B_102
      | ~ v2_funct_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102)))
      | ~ v1_funct_2(C_104,A_103,B_102)
      | ~ v1_funct_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_207,c_14])).

tff(c_329,plain,
    ( k8_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'),k2_struct_0('#skF_1')) = k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_325])).

tff(c_333,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k10_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_44,c_84,c_284,c_329])).

tff(c_195,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_tops_2(A_78,B_79,C_80) = k2_funct_1(C_80)
      | ~ v2_funct_1(C_80)
      | k2_relset_1(A_78,B_79,C_80) != B_79
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_funct_2(C_80,A_78,B_79)
      | ~ v1_funct_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_198,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_79,c_195])).

tff(c_201,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_76,c_84,c_44,c_198])).

tff(c_42,plain,
    ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_112,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1')
    | k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_66,c_66,c_67,c_67,c_66,c_66,c_42])).

tff(c_113,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_202,plain,(
    k1_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_113])).

tff(c_334,plain,(
    k10_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_1')) != k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_202])).

tff(c_347,plain,
    ( k9_relat_1('#skF_3',k2_struct_0('#skF_1')) != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_334])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_52,c_44,c_141,c_347])).

tff(c_351,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_446,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_351])).

tff(c_592,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_446])).

tff(c_599,plain,
    ( k10_relat_1('#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_592])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_52,c_44,c_407,c_599])).

tff(c_603,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_406])).

tff(c_38,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(k2_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_624,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_38])).

tff(c_628,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_624])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_628])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:15:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.47  %$ v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.17/1.47  
% 3.17/1.47  %Foreground sorts:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Background operators:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Foreground operators:
% 3.17/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.17/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.17/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.47  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.17/1.47  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.47  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.17/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.47  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.17/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.17/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.17/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.17/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.17/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.47  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.17/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.17/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.17/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.47  
% 3.30/1.49  tff(f_142, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.30/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.30/1.49  tff(f_98, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.30/1.49  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.30/1.49  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.30/1.49  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.30/1.49  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.30/1.49  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 3.30/1.49  tff(f_94, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.30/1.49  tff(f_50, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.30/1.49  tff(f_118, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.30/1.49  tff(f_34, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 3.30/1.49  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.30/1.49  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_54, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.30/1.49  tff(c_58, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_59, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.30/1.49  tff(c_67, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_59])).
% 3.30/1.49  tff(c_66, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_59])).
% 3.30/1.49  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_66, c_48])).
% 3.30/1.49  tff(c_8, plain, (![C_7, A_5, B_6]: (v1_relat_1(C_7) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.30/1.49  tff(c_83, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_8])).
% 3.30/1.49  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_50, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_76, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_66, c_50])).
% 3.30/1.49  tff(c_108, plain, (![A_44, B_45, C_46, D_47]: (k8_relset_1(A_44, B_45, C_46, D_47)=k10_relat_1(C_46, D_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.30/1.49  tff(c_111, plain, (![D_47]: (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_47)=k10_relat_1('#skF_3', D_47))), inference(resolution, [status(thm)], [c_79, c_108])).
% 3.30/1.49  tff(c_386, plain, (![A_120, B_121, C_122]: (k8_relset_1(A_120, B_121, C_122, B_121)=k1_relset_1(A_120, B_121, C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.30/1.49  tff(c_388, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_79, c_386])).
% 3.30/1.49  tff(c_390, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k10_relat_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_388])).
% 3.30/1.49  tff(c_400, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.30/1.49  tff(c_403, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_1') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_79, c_400])).
% 3.30/1.49  tff(c_406, plain, (k2_struct_0('#skF_2')=k1_xboole_0 | k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_390, c_403])).
% 3.30/1.49  tff(c_407, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_406])).
% 3.30/1.49  tff(c_6, plain, (![B_4, A_3]: (k9_relat_1(k2_funct_1(B_4), A_3)=k10_relat_1(B_4, A_3) | ~v2_funct_1(B_4) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.30/1.49  tff(c_46, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_84, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_66, c_46])).
% 3.30/1.49  tff(c_455, plain, (![C_140, B_141, A_142]: (m1_subset_1(k2_funct_1(C_140), k1_zfmisc_1(k2_zfmisc_1(B_141, A_142))) | k2_relset_1(A_142, B_141, C_140)!=B_141 | ~v2_funct_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_142, B_141))) | ~v1_funct_2(C_140, A_142, B_141) | ~v1_funct_1(C_140))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.30/1.49  tff(c_10, plain, (![A_8, B_9, C_10, D_11]: (k7_relset_1(A_8, B_9, C_10, D_11)=k9_relat_1(C_10, D_11) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.30/1.49  tff(c_518, plain, (![B_146, A_147, C_148, D_149]: (k7_relset_1(B_146, A_147, k2_funct_1(C_148), D_149)=k9_relat_1(k2_funct_1(C_148), D_149) | k2_relset_1(A_147, B_146, C_148)!=B_146 | ~v2_funct_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))) | ~v1_funct_2(C_148, A_147, B_146) | ~v1_funct_1(C_148))), inference(resolution, [status(thm)], [c_455, c_10])).
% 3.30/1.49  tff(c_522, plain, (![D_149]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_149)=k9_relat_1(k2_funct_1('#skF_3'), D_149) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_79, c_518])).
% 3.30/1.49  tff(c_526, plain, (![D_149]: (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_149)=k9_relat_1(k2_funct_1('#skF_3'), D_149))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_44, c_84, c_522])).
% 3.30/1.49  tff(c_16, plain, (![A_16, B_17, C_18]: (k7_relset_1(A_16, B_17, C_18, A_16)=k2_relset_1(A_16, B_17, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.30/1.49  tff(c_583, plain, (![B_161, A_162, C_163]: (k7_relset_1(B_161, A_162, k2_funct_1(C_163), B_161)=k2_relset_1(B_161, A_162, k2_funct_1(C_163)) | k2_relset_1(A_162, B_161, C_163)!=B_161 | ~v2_funct_1(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))) | ~v1_funct_2(C_163, A_162, B_161) | ~v1_funct_1(C_163))), inference(resolution, [status(thm)], [c_455, c_16])).
% 3.30/1.49  tff(c_587, plain, (k7_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))=k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_583])).
% 3.30/1.49  tff(c_591, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_44, c_84, c_526, c_587])).
% 3.30/1.49  tff(c_438, plain, (![A_137, B_138, C_139]: (k2_tops_2(A_137, B_138, C_139)=k2_funct_1(C_139) | ~v2_funct_1(C_139) | k2_relset_1(A_137, B_138, C_139)!=B_138 | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_2(C_139, A_137, B_138) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.30/1.49  tff(c_441, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_438])).
% 3.30/1.49  tff(c_444, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_84, c_44, c_441])).
% 3.30/1.49  tff(c_123, plain, (![A_49, B_50, C_51, D_52]: (k7_relset_1(A_49, B_50, C_51, D_52)=k9_relat_1(C_51, D_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.30/1.49  tff(c_126, plain, (![D_52]: (k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', D_52)=k9_relat_1('#skF_3', D_52))), inference(resolution, [status(thm)], [c_79, c_123])).
% 3.30/1.49  tff(c_137, plain, (![A_56, B_57, C_58]: (k7_relset_1(A_56, B_57, C_58, A_56)=k2_relset_1(A_56, B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.30/1.49  tff(c_139, plain, (k7_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_1'))=k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_79, c_137])).
% 3.30/1.49  tff(c_141, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_84, c_139])).
% 3.30/1.49  tff(c_4, plain, (![B_2, A_1]: (k10_relat_1(k2_funct_1(B_2), A_1)=k9_relat_1(B_2, A_1) | ~v2_funct_1(B_2) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.30/1.49  tff(c_207, plain, (![C_81, B_82, A_83]: (m1_subset_1(k2_funct_1(C_81), k1_zfmisc_1(k2_zfmisc_1(B_82, A_83))) | k2_relset_1(A_83, B_82, C_81)!=B_82 | ~v2_funct_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))) | ~v1_funct_2(C_81, A_83, B_82) | ~v1_funct_1(C_81))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.30/1.49  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k8_relset_1(A_12, B_13, C_14, D_15)=k10_relat_1(C_14, D_15) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.30/1.49  tff(c_276, plain, (![B_89, A_90, C_91, D_92]: (k8_relset_1(B_89, A_90, k2_funct_1(C_91), D_92)=k10_relat_1(k2_funct_1(C_91), D_92) | k2_relset_1(A_90, B_89, C_91)!=B_89 | ~v2_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))) | ~v1_funct_2(C_91, A_90, B_89) | ~v1_funct_1(C_91))), inference(resolution, [status(thm)], [c_207, c_12])).
% 3.30/1.49  tff(c_280, plain, (![D_92]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_92)=k10_relat_1(k2_funct_1('#skF_3'), D_92) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_79, c_276])).
% 3.30/1.49  tff(c_284, plain, (![D_92]: (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), D_92)=k10_relat_1(k2_funct_1('#skF_3'), D_92))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_44, c_84, c_280])).
% 3.30/1.49  tff(c_14, plain, (![A_16, B_17, C_18]: (k8_relset_1(A_16, B_17, C_18, B_17)=k1_relset_1(A_16, B_17, C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.30/1.49  tff(c_325, plain, (![B_102, A_103, C_104]: (k8_relset_1(B_102, A_103, k2_funct_1(C_104), A_103)=k1_relset_1(B_102, A_103, k2_funct_1(C_104)) | k2_relset_1(A_103, B_102, C_104)!=B_102 | ~v2_funct_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))) | ~v1_funct_2(C_104, A_103, B_102) | ~v1_funct_1(C_104))), inference(resolution, [status(thm)], [c_207, c_14])).
% 3.30/1.49  tff(c_329, plain, (k8_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'), k2_struct_0('#skF_1'))=k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_325])).
% 3.30/1.49  tff(c_333, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k10_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_44, c_84, c_284, c_329])).
% 3.30/1.49  tff(c_195, plain, (![A_78, B_79, C_80]: (k2_tops_2(A_78, B_79, C_80)=k2_funct_1(C_80) | ~v2_funct_1(C_80) | k2_relset_1(A_78, B_79, C_80)!=B_79 | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_funct_2(C_80, A_78, B_79) | ~v1_funct_1(C_80))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.30/1.49  tff(c_198, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_79, c_195])).
% 3.30/1.49  tff(c_201, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_76, c_84, c_44, c_198])).
% 3.30/1.49  tff(c_42, plain, (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.30/1.49  tff(c_112, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1') | k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_66, c_66, c_67, c_67, c_66, c_66, c_42])).
% 3.30/1.49  tff(c_113, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_112])).
% 3.30/1.49  tff(c_202, plain, (k1_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_113])).
% 3.30/1.49  tff(c_334, plain, (k10_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_1'))!=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_202])).
% 3.30/1.49  tff(c_347, plain, (k9_relat_1('#skF_3', k2_struct_0('#skF_1'))!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4, c_334])).
% 3.30/1.49  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_52, c_44, c_141, c_347])).
% 3.30/1.49  tff(c_351, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3'))!=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_112])).
% 3.30/1.49  tff(c_446, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_351])).
% 3.30/1.49  tff(c_592, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_591, c_446])).
% 3.30/1.49  tff(c_599, plain, (k10_relat_1('#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_592])).
% 3.30/1.49  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_52, c_44, c_407, c_599])).
% 3.30/1.49  tff(c_603, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_406])).
% 3.30/1.49  tff(c_38, plain, (![A_26]: (~v1_xboole_0(k2_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.30/1.49  tff(c_624, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_603, c_38])).
% 3.30/1.49  tff(c_628, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_624])).
% 3.30/1.49  tff(c_630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_628])).
% 3.30/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.49  
% 3.30/1.49  Inference rules
% 3.30/1.49  ----------------------
% 3.30/1.49  #Ref     : 0
% 3.30/1.49  #Sup     : 135
% 3.30/1.49  #Fact    : 0
% 3.30/1.49  #Define  : 0
% 3.30/1.49  #Split   : 3
% 3.30/1.49  #Chain   : 0
% 3.30/1.49  #Close   : 0
% 3.30/1.49  
% 3.30/1.49  Ordering : KBO
% 3.30/1.49  
% 3.30/1.49  Simplification rules
% 3.30/1.49  ----------------------
% 3.30/1.49  #Subsume      : 4
% 3.30/1.49  #Demod        : 139
% 3.30/1.49  #Tautology    : 64
% 3.30/1.49  #SimpNegUnit  : 1
% 3.30/1.49  #BackRed      : 17
% 3.30/1.49  
% 3.30/1.49  #Partial instantiations: 0
% 3.30/1.49  #Strategies tried      : 1
% 3.30/1.49  
% 3.30/1.49  Timing (in seconds)
% 3.30/1.49  ----------------------
% 3.30/1.50  Preprocessing        : 0.34
% 3.30/1.50  Parsing              : 0.18
% 3.30/1.50  CNF conversion       : 0.02
% 3.30/1.50  Main loop            : 0.37
% 3.30/1.50  Inferencing          : 0.13
% 3.30/1.50  Reduction            : 0.12
% 3.30/1.50  Demodulation         : 0.08
% 3.30/1.50  BG Simplification    : 0.02
% 3.30/1.50  Subsumption          : 0.07
% 3.30/1.50  Abstraction          : 0.02
% 3.30/1.50  MUC search           : 0.00
% 3.30/1.50  Cooper               : 0.00
% 3.30/1.50  Total                : 0.75
% 3.30/1.50  Index Insertion      : 0.00
% 3.30/1.50  Index Deletion       : 0.00
% 3.30/1.50  Index Matching       : 0.00
% 3.30/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
