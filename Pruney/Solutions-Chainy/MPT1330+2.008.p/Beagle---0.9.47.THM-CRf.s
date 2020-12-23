%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:10 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  151 (1210 expanded)
%              Number of leaves         :   45 ( 429 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 (2842 expanded)
%              Number of equality atoms :   75 (1130 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_121,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1531,plain,(
    ! [A_165,B_166] :
      ( v1_xboole_0(k2_zfmisc_1(A_165,B_166))
      | ~ v1_xboole_0(B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1537,plain,(
    ! [A_167,B_168] :
      ( k2_zfmisc_1(A_167,B_168) = k1_xboole_0
      | ~ v1_xboole_0(B_168) ) ),
    inference(resolution,[status(thm)],[c_1531,c_4])).

tff(c_1543,plain,(
    ! [A_167] : k2_zfmisc_1(A_167,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_1537])).

tff(c_18,plain,(
    ! [A_9] : k9_relat_1(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( v1_xboole_0(k2_zfmisc_1(A_3,B_4))
      | ~ v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,(
    ! [A_40,B_41] :
      ( v1_xboole_0(k2_zfmisc_1(A_40,B_41))
      | ~ v1_xboole_0(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_99,plain,(
    ! [A_44,B_45] :
      ( k2_zfmisc_1(A_44,B_45) = k1_xboole_0
      | ~ v1_xboole_0(B_45) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_273,plain,(
    ! [A_69,A_70,B_71] :
      ( k2_zfmisc_1(A_69,k2_zfmisc_1(A_70,B_71)) = k1_xboole_0
      | ~ v1_xboole_0(B_71) ) ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_128,plain,(
    ! [A_49] : m1_subset_1(k6_relat_1(A_49),k1_zfmisc_1(k2_zfmisc_1(A_49,A_49))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_136,plain,(
    ! [A_49] : r1_tarski(k6_relat_1(A_49),k2_zfmisc_1(A_49,A_49)) ),
    inference(resolution,[status(thm)],[c_128,c_10])).

tff(c_348,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k6_relat_1(k2_zfmisc_1(A_76,B_77)),k1_xboole_0)
      | ~ v1_xboole_0(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_136])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_363,plain,(
    ! [A_76,B_77] :
      ( k6_relat_1(k2_zfmisc_1(A_76,B_77)) = k1_xboole_0
      | ~ v1_xboole_0(B_77) ) ),
    inference(resolution,[status(thm)],[c_348,c_6])).

tff(c_58,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_82,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_74])).

tff(c_56,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_81,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_74])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_123,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_50])).

tff(c_317,plain,(
    ! [A_72,B_73] :
      ( k9_relat_1(k6_relat_1(A_72),B_73) = B_73
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_333,plain,(
    k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_123,c_317])).

tff(c_412,plain,
    ( k9_relat_1(k1_xboole_0,'#skF_3') = '#skF_3'
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_333])).

tff(c_421,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_412])).

tff(c_425,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_160,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_174,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_160])).

tff(c_464,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_482,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_123,c_464])).

tff(c_564,plain,(
    ! [B_97,A_98] :
      ( k1_relat_1(B_97) = A_98
      | ~ v1_partfun1(B_97,A_98)
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_573,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_482,c_564])).

tff(c_585,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_573])).

tff(c_745,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_83,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_52])).

tff(c_97,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_83])).

tff(c_1107,plain,(
    ! [C_142,A_143,B_144] :
      ( v1_partfun1(C_142,A_143)
      | ~ v1_funct_2(C_142,A_143,B_144)
      | ~ v1_funct_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | v1_xboole_0(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1116,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_123,c_1107])).

tff(c_1127,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_97,c_1116])).

tff(c_1129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_425,c_745,c_1127])).

tff(c_1130,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_46,plain,(
    k8_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_179,plain,(
    k8_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_81,c_46])).

tff(c_1136,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1130,c_179])).

tff(c_663,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_681,plain,(
    k1_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_663])).

tff(c_1132,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_681])).

tff(c_1137,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_123])).

tff(c_1375,plain,(
    ! [A_156,B_157,C_158] :
      ( k8_relset_1(A_156,B_157,C_158,B_157) = k1_relset_1(A_156,B_157,C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1377,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1137,c_1375])).

tff(c_1388,plain,(
    k8_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_1377])).

tff(c_1390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1136,c_1388])).

tff(c_1391,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_48,plain,
    ( k2_struct_0('#skF_1') = k1_xboole_0
    | k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_73,plain,(
    k2_struct_0('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1407,plain,(
    k2_struct_0('#skF_2') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_73])).

tff(c_1392,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_1487,plain,(
    ! [A_163] :
      ( A_163 = '#skF_3'
      | ~ v1_xboole_0(A_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_4])).

tff(c_1490,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1392,c_1487])).

tff(c_1500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1407,c_1490])).

tff(c_1501,plain,(
    k2_struct_0('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1511,plain,(
    ! [A_164] :
      ( u1_struct_0(A_164) = k2_struct_0(A_164)
      | ~ l1_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1517,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1511])).

tff(c_1521,plain,(
    u1_struct_0('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1501,c_1517])).

tff(c_1502,plain,(
    k2_struct_0('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1514,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1511])).

tff(c_1519,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1502,c_1514])).

tff(c_1556,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1543,c_1521,c_1519,c_50])).

tff(c_1562,plain,(
    ! [A_171,B_172] :
      ( r1_tarski(A_171,B_172)
      | ~ m1_subset_1(A_171,k1_zfmisc_1(B_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1574,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1556,c_1562])).

tff(c_1578,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1574,c_6])).

tff(c_1586,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1519])).

tff(c_1587,plain,(
    k2_struct_0('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1502])).

tff(c_1588,plain,(
    k2_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1501])).

tff(c_1585,plain,(
    u1_struct_0('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1521])).

tff(c_1610,plain,(
    k8_relset_1('#skF_3',u1_struct_0('#skF_2'),'#skF_3',k2_struct_0('#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1588,c_1585,c_46])).

tff(c_1611,plain,(
    k8_relset_1('#skF_3',u1_struct_0('#skF_2'),'#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_1610])).

tff(c_1665,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_1611])).

tff(c_30,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1626,plain,(
    ! [C_175,A_176,B_177] :
      ( v1_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1635,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(resolution,[status(thm)],[c_30,c_1626])).

tff(c_1557,plain,(
    ! [A_170] : m1_subset_1(k6_relat_1(A_170),k1_zfmisc_1(k2_zfmisc_1(A_170,A_170))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1561,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1543,c_1557])).

tff(c_1572,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1561,c_1562])).

tff(c_1620,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1578,c_1572])).

tff(c_1673,plain,(
    ! [A_182] :
      ( A_182 = '#skF_3'
      | ~ r1_tarski(A_182,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1578,c_6])).

tff(c_1680,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1620,c_1673])).

tff(c_1798,plain,(
    ! [C_200,A_201,B_202] :
      ( v4_relat_1(C_200,A_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1810,plain,(
    ! [A_21] : v4_relat_1(k6_relat_1(A_21),A_21) ),
    inference(resolution,[status(thm)],[c_30,c_1798])).

tff(c_1721,plain,(
    ! [B_186,A_187] :
      ( r1_tarski(k1_relat_1(B_186),A_187)
      | ~ v4_relat_1(B_186,A_187)
      | ~ v1_relat_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1589,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ r1_tarski(A_2,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_1578,c_6])).

tff(c_1937,plain,(
    ! [B_224] :
      ( k1_relat_1(B_224) = '#skF_3'
      | ~ v4_relat_1(B_224,'#skF_3')
      | ~ v1_relat_1(B_224) ) ),
    inference(resolution,[status(thm)],[c_1721,c_1589])).

tff(c_1949,plain,
    ( k1_relat_1(k6_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1810,c_1937])).

tff(c_1956,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1635,c_1680,c_1949])).

tff(c_2060,plain,(
    ! [A_233,B_234,C_235] :
      ( k1_relset_1(A_233,B_234,C_235) = k1_relat_1(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2075,plain,(
    ! [A_21] : k1_relset_1(A_21,A_21,k6_relat_1(A_21)) = k1_relat_1(k6_relat_1(A_21)) ),
    inference(resolution,[status(thm)],[c_30,c_2060])).

tff(c_2299,plain,(
    ! [A_250,B_251,C_252] :
      ( k8_relset_1(A_250,B_251,C_252,B_251) = k1_relset_1(A_250,B_251,C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_250,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2308,plain,(
    ! [A_21] : k8_relset_1(A_21,A_21,k6_relat_1(A_21),A_21) = k1_relset_1(A_21,A_21,k6_relat_1(A_21)) ),
    inference(resolution,[status(thm)],[c_30,c_2299])).

tff(c_2322,plain,(
    ! [A_254] : k8_relset_1(A_254,A_254,k6_relat_1(A_254),A_254) = k1_relat_1(k6_relat_1(A_254)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2075,c_2308])).

tff(c_2334,plain,(
    k1_relat_1(k6_relat_1('#skF_3')) = k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1680,c_2322])).

tff(c_2337,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1956,c_1680,c_2334])).

tff(c_2339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1665,c_2337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:25:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.71  
% 3.98/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.98/1.71  
% 3.98/1.71  %Foreground sorts:
% 3.98/1.71  
% 3.98/1.71  
% 3.98/1.71  %Background operators:
% 3.98/1.71  
% 3.98/1.71  
% 3.98/1.71  %Foreground operators:
% 3.98/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.98/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.98/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.71  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.98/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.71  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.98/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.98/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.98/1.71  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.98/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.98/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.98/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.98/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.71  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.98/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.98/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.98/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.98/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.98/1.71  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.98/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.98/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.98/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.71  
% 3.98/1.73  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.98/1.73  tff(f_38, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.98/1.73  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.98/1.73  tff(f_50, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 3.98/1.73  tff(f_70, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.98/1.73  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.98/1.73  tff(f_34, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.98/1.73  tff(f_121, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 3.98/1.73  tff(f_102, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.98/1.73  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 3.98/1.73  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.98/1.73  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.98/1.73  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.98/1.73  tff(f_90, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.98/1.73  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.98/1.73  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.98/1.73  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.98/1.73  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.98/1.73  tff(c_1531, plain, (![A_165, B_166]: (v1_xboole_0(k2_zfmisc_1(A_165, B_166)) | ~v1_xboole_0(B_166))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.98/1.73  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.98/1.73  tff(c_1537, plain, (![A_167, B_168]: (k2_zfmisc_1(A_167, B_168)=k1_xboole_0 | ~v1_xboole_0(B_168))), inference(resolution, [status(thm)], [c_1531, c_4])).
% 3.98/1.73  tff(c_1543, plain, (![A_167]: (k2_zfmisc_1(A_167, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_1537])).
% 3.98/1.73  tff(c_18, plain, (![A_9]: (k9_relat_1(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.98/1.73  tff(c_8, plain, (![A_3, B_4]: (v1_xboole_0(k2_zfmisc_1(A_3, B_4)) | ~v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.98/1.73  tff(c_92, plain, (![A_40, B_41]: (v1_xboole_0(k2_zfmisc_1(A_40, B_41)) | ~v1_xboole_0(B_41))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.98/1.73  tff(c_99, plain, (![A_44, B_45]: (k2_zfmisc_1(A_44, B_45)=k1_xboole_0 | ~v1_xboole_0(B_45))), inference(resolution, [status(thm)], [c_92, c_4])).
% 3.98/1.73  tff(c_273, plain, (![A_69, A_70, B_71]: (k2_zfmisc_1(A_69, k2_zfmisc_1(A_70, B_71))=k1_xboole_0 | ~v1_xboole_0(B_71))), inference(resolution, [status(thm)], [c_8, c_99])).
% 3.98/1.73  tff(c_128, plain, (![A_49]: (m1_subset_1(k6_relat_1(A_49), k1_zfmisc_1(k2_zfmisc_1(A_49, A_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.73  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.98/1.73  tff(c_136, plain, (![A_49]: (r1_tarski(k6_relat_1(A_49), k2_zfmisc_1(A_49, A_49)))), inference(resolution, [status(thm)], [c_128, c_10])).
% 3.98/1.73  tff(c_348, plain, (![A_76, B_77]: (r1_tarski(k6_relat_1(k2_zfmisc_1(A_76, B_77)), k1_xboole_0) | ~v1_xboole_0(B_77))), inference(superposition, [status(thm), theory('equality')], [c_273, c_136])).
% 3.98/1.73  tff(c_6, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.98/1.73  tff(c_363, plain, (![A_76, B_77]: (k6_relat_1(k2_zfmisc_1(A_76, B_77))=k1_xboole_0 | ~v1_xboole_0(B_77))), inference(resolution, [status(thm)], [c_348, c_6])).
% 3.98/1.73  tff(c_58, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.98/1.73  tff(c_74, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.98/1.73  tff(c_82, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_74])).
% 3.98/1.73  tff(c_56, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.98/1.73  tff(c_81, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_74])).
% 3.98/1.73  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.98/1.73  tff(c_123, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_50])).
% 3.98/1.73  tff(c_317, plain, (![A_72, B_73]: (k9_relat_1(k6_relat_1(A_72), B_73)=B_73 | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.98/1.73  tff(c_333, plain, (k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_123, c_317])).
% 3.98/1.73  tff(c_412, plain, (k9_relat_1(k1_xboole_0, '#skF_3')='#skF_3' | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_363, c_333])).
% 3.98/1.73  tff(c_421, plain, (k1_xboole_0='#skF_3' | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_412])).
% 3.98/1.73  tff(c_425, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_421])).
% 3.98/1.73  tff(c_160, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.73  tff(c_174, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_160])).
% 3.98/1.73  tff(c_464, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.73  tff(c_482, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_123, c_464])).
% 3.98/1.73  tff(c_564, plain, (![B_97, A_98]: (k1_relat_1(B_97)=A_98 | ~v1_partfun1(B_97, A_98) | ~v4_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.98/1.73  tff(c_573, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_482, c_564])).
% 3.98/1.73  tff(c_585, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_573])).
% 3.98/1.73  tff(c_745, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_585])).
% 3.98/1.73  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.98/1.73  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.98/1.73  tff(c_83, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_52])).
% 3.98/1.73  tff(c_97, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_83])).
% 3.98/1.73  tff(c_1107, plain, (![C_142, A_143, B_144]: (v1_partfun1(C_142, A_143) | ~v1_funct_2(C_142, A_143, B_144) | ~v1_funct_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | v1_xboole_0(B_144))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.98/1.73  tff(c_1116, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_123, c_1107])).
% 3.98/1.73  tff(c_1127, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_97, c_1116])).
% 3.98/1.73  tff(c_1129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_425, c_745, c_1127])).
% 3.98/1.73  tff(c_1130, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_585])).
% 3.98/1.73  tff(c_46, plain, (k8_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.98/1.73  tff(c_179, plain, (k8_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_81, c_46])).
% 3.98/1.73  tff(c_1136, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1130, c_179])).
% 3.98/1.73  tff(c_663, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.98/1.73  tff(c_681, plain, (k1_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_123, c_663])).
% 3.98/1.73  tff(c_1132, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_681])).
% 3.98/1.73  tff(c_1137, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_123])).
% 3.98/1.73  tff(c_1375, plain, (![A_156, B_157, C_158]: (k8_relset_1(A_156, B_157, C_158, B_157)=k1_relset_1(A_156, B_157, C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.98/1.73  tff(c_1377, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1137, c_1375])).
% 3.98/1.73  tff(c_1388, plain, (k8_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_1377])).
% 3.98/1.73  tff(c_1390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1136, c_1388])).
% 3.98/1.73  tff(c_1391, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_421])).
% 3.98/1.73  tff(c_48, plain, (k2_struct_0('#skF_1')=k1_xboole_0 | k2_struct_0('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.98/1.73  tff(c_73, plain, (k2_struct_0('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 3.98/1.73  tff(c_1407, plain, (k2_struct_0('#skF_2')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_73])).
% 3.98/1.73  tff(c_1392, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_421])).
% 3.98/1.73  tff(c_1487, plain, (![A_163]: (A_163='#skF_3' | ~v1_xboole_0(A_163))), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_4])).
% 3.98/1.73  tff(c_1490, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_1392, c_1487])).
% 3.98/1.73  tff(c_1500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1407, c_1490])).
% 3.98/1.73  tff(c_1501, plain, (k2_struct_0('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.98/1.73  tff(c_1511, plain, (![A_164]: (u1_struct_0(A_164)=k2_struct_0(A_164) | ~l1_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.98/1.73  tff(c_1517, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_1511])).
% 3.98/1.73  tff(c_1521, plain, (u1_struct_0('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1501, c_1517])).
% 3.98/1.73  tff(c_1502, plain, (k2_struct_0('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 3.98/1.73  tff(c_1514, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1511])).
% 3.98/1.73  tff(c_1519, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1502, c_1514])).
% 3.98/1.73  tff(c_1556, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1543, c_1521, c_1519, c_50])).
% 3.98/1.73  tff(c_1562, plain, (![A_171, B_172]: (r1_tarski(A_171, B_172) | ~m1_subset_1(A_171, k1_zfmisc_1(B_172)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.98/1.73  tff(c_1574, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1556, c_1562])).
% 3.98/1.73  tff(c_1578, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1574, c_6])).
% 3.98/1.73  tff(c_1586, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1519])).
% 3.98/1.73  tff(c_1587, plain, (k2_struct_0('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1502])).
% 3.98/1.73  tff(c_1588, plain, (k2_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1501])).
% 3.98/1.73  tff(c_1585, plain, (u1_struct_0('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1521])).
% 3.98/1.73  tff(c_1610, plain, (k8_relset_1('#skF_3', u1_struct_0('#skF_2'), '#skF_3', k2_struct_0('#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1588, c_1585, c_46])).
% 3.98/1.73  tff(c_1611, plain, (k8_relset_1('#skF_3', u1_struct_0('#skF_2'), '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_1610])).
% 3.98/1.73  tff(c_1665, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_1611])).
% 3.98/1.73  tff(c_30, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.73  tff(c_1626, plain, (![C_175, A_176, B_177]: (v1_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.98/1.73  tff(c_1635, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(resolution, [status(thm)], [c_30, c_1626])).
% 3.98/1.73  tff(c_1557, plain, (![A_170]: (m1_subset_1(k6_relat_1(A_170), k1_zfmisc_1(k2_zfmisc_1(A_170, A_170))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.98/1.73  tff(c_1561, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1543, c_1557])).
% 3.98/1.73  tff(c_1572, plain, (r1_tarski(k6_relat_1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_1561, c_1562])).
% 3.98/1.73  tff(c_1620, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1578, c_1572])).
% 3.98/1.73  tff(c_1673, plain, (![A_182]: (A_182='#skF_3' | ~r1_tarski(A_182, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1578, c_6])).
% 3.98/1.73  tff(c_1680, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1620, c_1673])).
% 3.98/1.73  tff(c_1798, plain, (![C_200, A_201, B_202]: (v4_relat_1(C_200, A_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.98/1.73  tff(c_1810, plain, (![A_21]: (v4_relat_1(k6_relat_1(A_21), A_21))), inference(resolution, [status(thm)], [c_30, c_1798])).
% 3.98/1.73  tff(c_1721, plain, (![B_186, A_187]: (r1_tarski(k1_relat_1(B_186), A_187) | ~v4_relat_1(B_186, A_187) | ~v1_relat_1(B_186))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.98/1.73  tff(c_1589, plain, (![A_2]: (A_2='#skF_3' | ~r1_tarski(A_2, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_1578, c_6])).
% 3.98/1.73  tff(c_1937, plain, (![B_224]: (k1_relat_1(B_224)='#skF_3' | ~v4_relat_1(B_224, '#skF_3') | ~v1_relat_1(B_224))), inference(resolution, [status(thm)], [c_1721, c_1589])).
% 3.98/1.73  tff(c_1949, plain, (k1_relat_1(k6_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1810, c_1937])).
% 3.98/1.73  tff(c_1956, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1635, c_1680, c_1949])).
% 3.98/1.73  tff(c_2060, plain, (![A_233, B_234, C_235]: (k1_relset_1(A_233, B_234, C_235)=k1_relat_1(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.98/1.73  tff(c_2075, plain, (![A_21]: (k1_relset_1(A_21, A_21, k6_relat_1(A_21))=k1_relat_1(k6_relat_1(A_21)))), inference(resolution, [status(thm)], [c_30, c_2060])).
% 3.98/1.73  tff(c_2299, plain, (![A_250, B_251, C_252]: (k8_relset_1(A_250, B_251, C_252, B_251)=k1_relset_1(A_250, B_251, C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_250, B_251))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.98/1.73  tff(c_2308, plain, (![A_21]: (k8_relset_1(A_21, A_21, k6_relat_1(A_21), A_21)=k1_relset_1(A_21, A_21, k6_relat_1(A_21)))), inference(resolution, [status(thm)], [c_30, c_2299])).
% 3.98/1.73  tff(c_2322, plain, (![A_254]: (k8_relset_1(A_254, A_254, k6_relat_1(A_254), A_254)=k1_relat_1(k6_relat_1(A_254)))), inference(demodulation, [status(thm), theory('equality')], [c_2075, c_2308])).
% 3.98/1.73  tff(c_2334, plain, (k1_relat_1(k6_relat_1('#skF_3'))=k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1680, c_2322])).
% 3.98/1.73  tff(c_2337, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1956, c_1680, c_2334])).
% 3.98/1.73  tff(c_2339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1665, c_2337])).
% 3.98/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.73  
% 3.98/1.73  Inference rules
% 3.98/1.73  ----------------------
% 3.98/1.73  #Ref     : 0
% 3.98/1.73  #Sup     : 507
% 3.98/1.73  #Fact    : 0
% 3.98/1.73  #Define  : 0
% 3.98/1.73  #Split   : 3
% 3.98/1.73  #Chain   : 0
% 3.98/1.73  #Close   : 0
% 3.98/1.73  
% 3.98/1.73  Ordering : KBO
% 3.98/1.73  
% 3.98/1.73  Simplification rules
% 3.98/1.73  ----------------------
% 3.98/1.73  #Subsume      : 39
% 3.98/1.73  #Demod        : 444
% 3.98/1.73  #Tautology    : 279
% 3.98/1.73  #SimpNegUnit  : 4
% 3.98/1.73  #BackRed      : 50
% 3.98/1.73  
% 3.98/1.73  #Partial instantiations: 0
% 3.98/1.73  #Strategies tried      : 1
% 3.98/1.73  
% 3.98/1.73  Timing (in seconds)
% 3.98/1.73  ----------------------
% 3.98/1.73  Preprocessing        : 0.35
% 3.98/1.73  Parsing              : 0.19
% 3.98/1.73  CNF conversion       : 0.02
% 3.98/1.73  Main loop            : 0.58
% 3.98/1.73  Inferencing          : 0.21
% 3.98/1.73  Reduction            : 0.20
% 3.98/1.73  Demodulation         : 0.14
% 3.98/1.73  BG Simplification    : 0.02
% 3.98/1.73  Subsumption          : 0.09
% 3.98/1.73  Abstraction          : 0.03
% 3.98/1.73  MUC search           : 0.00
% 3.98/1.73  Cooper               : 0.00
% 3.98/1.73  Total                : 0.97
% 3.98/1.74  Index Insertion      : 0.00
% 3.98/1.74  Index Deletion       : 0.00
% 3.98/1.74  Index Matching       : 0.00
% 3.98/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
