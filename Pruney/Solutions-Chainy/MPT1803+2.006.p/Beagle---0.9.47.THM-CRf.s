%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:01 EST 2020

% Result     : Theorem 8.85s
% Output     : CNFRefutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :  199 (4367 expanded)
%              Number of leaves         :   43 (1557 expanded)
%              Depth                    :   50
%              Number of atoms          :  907 (23773 expanded)
%              Number of equality atoms :   94 (1915 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_tmap_1,type,(
    k9_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_222,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tmap_1(B,k8_tmap_1(A,B),k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).

tff(f_203,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_151,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) )
             => ( C = k9_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => r1_funct_2(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,D)),C,k7_tmap_1(A,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

tff(f_196,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_174,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( u1_struct_0(C) = B
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(C))
                   => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_tmap_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_44,plain,(
    ! [B_84,A_82] :
      ( m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_32,plain,(
    ! [A_58,B_59] :
      ( l1_pre_topc(k8_tmap_1(A_58,B_59))
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_36,plain,(
    ! [A_58,B_59] :
      ( v1_pre_topc(k8_tmap_1(A_58,B_59))
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_34,plain,(
    ! [A_58,B_59] :
      ( v2_pre_topc(k8_tmap_1(A_58,B_59))
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_209,plain,(
    ! [A_145,B_146] :
      ( k6_tmap_1(A_145,u1_struct_0(B_146)) = k8_tmap_1(A_145,B_146)
      | ~ m1_subset_1(u1_struct_0(B_146),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(k8_tmap_1(A_145,B_146))
      | ~ v2_pre_topc(k8_tmap_1(A_145,B_146))
      | ~ v1_pre_topc(k8_tmap_1(A_145,B_146))
      | ~ m1_pre_topc(B_146,A_145)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_220,plain,(
    ! [A_147,B_148] :
      ( k6_tmap_1(A_147,u1_struct_0(B_148)) = k8_tmap_1(A_147,B_148)
      | ~ l1_pre_topc(k8_tmap_1(A_147,B_148))
      | ~ v2_pre_topc(k8_tmap_1(A_147,B_148))
      | ~ v1_pre_topc(k8_tmap_1(A_147,B_148))
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147)
      | ~ m1_pre_topc(B_148,A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(resolution,[status(thm)],[c_44,c_209])).

tff(c_225,plain,(
    ! [A_149,B_150] :
      ( k6_tmap_1(A_149,u1_struct_0(B_150)) = k8_tmap_1(A_149,B_150)
      | ~ l1_pre_topc(k8_tmap_1(A_149,B_150))
      | ~ v1_pre_topc(k8_tmap_1(A_149,B_150))
      | ~ m1_pre_topc(B_150,A_149)
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_34,c_220])).

tff(c_230,plain,(
    ! [A_151,B_152] :
      ( k6_tmap_1(A_151,u1_struct_0(B_152)) = k8_tmap_1(A_151,B_152)
      | ~ l1_pre_topc(k8_tmap_1(A_151,B_152))
      | ~ m1_pre_topc(B_152,A_151)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_36,c_225])).

tff(c_234,plain,(
    ! [A_58,B_59] :
      ( k6_tmap_1(A_58,u1_struct_0(B_59)) = k8_tmap_1(A_58,B_59)
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_32,c_230])).

tff(c_71,plain,(
    ! [A_103,B_104] :
      ( k7_tmap_1(A_103,B_104) = k6_partfun1(u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    ! [A_105,B_106] :
      ( k7_tmap_1(A_105,u1_struct_0(B_106)) = k6_partfun1(u1_struct_0(A_105))
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105)
      | ~ m1_pre_topc(B_106,A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_65,plain,(
    ! [A_99,B_100] :
      ( v1_funct_1(k7_tmap_1(A_99,B_100))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_69,plain,(
    ! [A_82,B_84] :
      ( v1_funct_1(k7_tmap_1(A_82,u1_struct_0(B_84)))
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_44,c_65])).

tff(c_133,plain,(
    ! [A_115,B_116] :
      ( v1_funct_1(k6_partfun1(u1_struct_0(A_115)))
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115)
      | ~ m1_pre_topc(B_116,A_115)
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115)
      | v2_struct_0(A_115)
      | ~ m1_pre_topc(B_116,A_115)
      | ~ l1_pre_topc(A_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_69])).

tff(c_135,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_133])).

tff(c_138,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_56,c_135])).

tff(c_139,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_138])).

tff(c_75,plain,(
    ! [A_82,B_84] :
      ( k7_tmap_1(A_82,u1_struct_0(B_84)) = k6_partfun1(u1_struct_0(A_82))
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_118,plain,(
    ! [A_109,B_110] :
      ( v1_funct_2(k7_tmap_1(A_109,B_110),u1_struct_0(A_109),u1_struct_0(k6_tmap_1(A_109,B_110)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_259,plain,(
    ! [A_167,B_168] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_167)),u1_struct_0(A_167),u1_struct_0(k6_tmap_1(A_167,u1_struct_0(B_168))))
      | ~ m1_subset_1(u1_struct_0(B_168),k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167)
      | ~ m1_pre_topc(B_168,A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_118])).

tff(c_262,plain,(
    ! [A_58,B_59] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_58)),u1_struct_0(A_58),u1_struct_0(k8_tmap_1(A_58,B_59)))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_259])).

tff(c_125,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k7_tmap_1(A_111,B_112),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(k6_tmap_1(A_111,B_112)))))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_309,plain,(
    ! [A_180,B_181] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_180)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_180),u1_struct_0(k6_tmap_1(A_180,u1_struct_0(B_181))))))
      | ~ m1_subset_1(u1_struct_0(B_181),k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180)
      | ~ m1_pre_topc(B_181,A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_125])).

tff(c_500,plain,(
    ! [A_218,B_219] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_218)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_218),u1_struct_0(k8_tmap_1(A_218,B_219)))))
      | ~ m1_subset_1(u1_struct_0(B_219),k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218)
      | ~ m1_pre_topc(B_219,A_218)
      | ~ l1_pre_topc(A_218)
      | ~ m1_pre_topc(B_219,A_218)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_309])).

tff(c_22,plain,(
    ! [B_46,A_34,C_52] :
      ( u1_struct_0(B_46) = '#skF_2'(A_34,B_46,C_52)
      | k9_tmap_1(A_34,B_46) = C_52
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34),u1_struct_0(k8_tmap_1(A_34,B_46)))))
      | ~ v1_funct_2(C_52,u1_struct_0(A_34),u1_struct_0(k8_tmap_1(A_34,B_46)))
      | ~ v1_funct_1(C_52)
      | ~ m1_pre_topc(B_46,A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_521,plain,(
    ! [A_220,B_221] :
      ( '#skF_2'(A_220,B_221,k6_partfun1(u1_struct_0(A_220))) = u1_struct_0(B_221)
      | k9_tmap_1(A_220,B_221) = k6_partfun1(u1_struct_0(A_220))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_220)),u1_struct_0(A_220),u1_struct_0(k8_tmap_1(A_220,B_221)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_220)))
      | ~ m1_subset_1(u1_struct_0(B_221),k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ m1_pre_topc(B_221,A_220)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_500,c_22])).

tff(c_560,plain,(
    ! [A_224,B_225] :
      ( '#skF_2'(A_224,B_225,k6_partfun1(u1_struct_0(A_224))) = u1_struct_0(B_225)
      | k9_tmap_1(A_224,B_225) = k6_partfun1(u1_struct_0(A_224))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_224)))
      | ~ m1_subset_1(u1_struct_0(B_225),k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ m1_pre_topc(B_225,A_224)
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(resolution,[status(thm)],[c_262,c_521])).

tff(c_568,plain,(
    ! [A_226,B_227] :
      ( '#skF_2'(A_226,B_227,k6_partfun1(u1_struct_0(A_226))) = u1_struct_0(B_227)
      | k9_tmap_1(A_226,B_227) = k6_partfun1(u1_struct_0(A_226))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_226)))
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226)
      | ~ m1_pre_topc(B_227,A_226)
      | ~ l1_pre_topc(A_226) ) ),
    inference(resolution,[status(thm)],[c_44,c_560])).

tff(c_570,plain,(
    ! [B_227] :
      ( '#skF_2'('#skF_3',B_227,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_227)
      | k9_tmap_1('#skF_3',B_227) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_227,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_139,c_568])).

tff(c_575,plain,(
    ! [B_227] :
      ( '#skF_2'('#skF_3',B_227,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_227)
      | k9_tmap_1('#skF_3',B_227) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_227,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_570])).

tff(c_576,plain,(
    ! [B_227] :
      ( '#skF_2'('#skF_3',B_227,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_227)
      | k9_tmap_1('#skF_3',B_227) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_227,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_575])).

tff(c_24,plain,(
    ! [A_34,B_46,C_52] :
      ( m1_subset_1('#skF_2'(A_34,B_46,C_52),k1_zfmisc_1(u1_struct_0(A_34)))
      | k9_tmap_1(A_34,B_46) = C_52
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34),u1_struct_0(k8_tmap_1(A_34,B_46)))))
      | ~ v1_funct_2(C_52,u1_struct_0(A_34),u1_struct_0(k8_tmap_1(A_34,B_46)))
      | ~ v1_funct_1(C_52)
      | ~ m1_pre_topc(B_46,A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_661,plain,(
    ! [A_239,B_240] :
      ( m1_subset_1('#skF_2'(A_239,B_240,k6_partfun1(u1_struct_0(A_239))),k1_zfmisc_1(u1_struct_0(A_239)))
      | k9_tmap_1(A_239,B_240) = k6_partfun1(u1_struct_0(A_239))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_239)),u1_struct_0(A_239),u1_struct_0(k8_tmap_1(A_239,B_240)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_239)))
      | ~ m1_subset_1(u1_struct_0(B_240),k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ m1_pre_topc(B_240,A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_500,c_24])).

tff(c_697,plain,(
    ! [A_244,B_245] :
      ( m1_subset_1('#skF_2'(A_244,B_245,k6_partfun1(u1_struct_0(A_244))),k1_zfmisc_1(u1_struct_0(A_244)))
      | k9_tmap_1(A_244,B_245) = k6_partfun1(u1_struct_0(A_244))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_244)))
      | ~ m1_subset_1(u1_struct_0(B_245),k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ m1_pre_topc(B_245,A_244)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(resolution,[status(thm)],[c_262,c_661])).

tff(c_8,plain,(
    ! [A_9,B_11] :
      ( k7_tmap_1(A_9,B_11) = k6_partfun1(u1_struct_0(A_9))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_775,plain,(
    ! [A_253,B_254] :
      ( k7_tmap_1(A_253,'#skF_2'(A_253,B_254,k6_partfun1(u1_struct_0(A_253)))) = k6_partfun1(u1_struct_0(A_253))
      | k9_tmap_1(A_253,B_254) = k6_partfun1(u1_struct_0(A_253))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_253)))
      | ~ m1_subset_1(u1_struct_0(B_254),k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ m1_pre_topc(B_254,A_253)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(resolution,[status(thm)],[c_697,c_8])).

tff(c_783,plain,(
    ! [A_255,B_256] :
      ( k7_tmap_1(A_255,'#skF_2'(A_255,B_256,k6_partfun1(u1_struct_0(A_255)))) = k6_partfun1(u1_struct_0(A_255))
      | k9_tmap_1(A_255,B_256) = k6_partfun1(u1_struct_0(A_255))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_255)))
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255)
      | ~ m1_pre_topc(B_256,A_255)
      | ~ l1_pre_topc(A_255) ) ),
    inference(resolution,[status(thm)],[c_44,c_775])).

tff(c_820,plain,(
    ! [B_227] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_227)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k9_tmap_1('#skF_3',B_227) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_227,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | k9_tmap_1('#skF_3',B_227) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_227,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_783])).

tff(c_833,plain,(
    ! [B_227] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_227)) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_227) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_227,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_139,c_820])).

tff(c_835,plain,(
    ! [B_257] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_257)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k9_tmap_1('#skF_3',B_257) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_257,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_833])).

tff(c_42,plain,(
    ! [A_75,B_79] :
      ( u1_struct_0(k8_tmap_1(A_75,B_79)) = u1_struct_0(A_75)
      | ~ m1_pre_topc(B_79,A_75)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_239,plain,(
    ! [A_159,B_160] :
      ( k6_tmap_1(A_159,u1_struct_0(B_160)) = k8_tmap_1(A_159,B_160)
      | ~ m1_pre_topc(B_160,A_159)
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_32,c_230])).

tff(c_28,plain,(
    ! [A_56,B_57] :
      ( v1_funct_2(k7_tmap_1(A_56,B_57),u1_struct_0(A_56),u1_struct_0(k6_tmap_1(A_56,B_57)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_272,plain,(
    ! [A_169,B_170] :
      ( v1_funct_2(k7_tmap_1(A_169,u1_struct_0(B_170)),u1_struct_0(A_169),u1_struct_0(k8_tmap_1(A_169,B_170)))
      | ~ m1_subset_1(u1_struct_0(B_170),k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169)
      | ~ m1_pre_topc(B_170,A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_28])).

tff(c_281,plain,(
    ! [A_75,B_79] :
      ( v1_funct_2(k7_tmap_1(A_75,u1_struct_0(B_79)),u1_struct_0(A_75),u1_struct_0(A_75))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75)
      | ~ m1_pre_topc(B_79,A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75)
      | ~ m1_pre_topc(B_79,A_75)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_272])).

tff(c_850,plain,(
    ! [B_257] :
      ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_257),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_257,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_257,'#skF_3')
      | v2_struct_0(B_257)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_257) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_257,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_281])).

tff(c_891,plain,(
    ! [B_257] :
      ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_257),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_257)
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_257) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_257,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_56,c_54,c_56,c_54,c_850])).

tff(c_892,plain,(
    ! [B_257] :
      ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_257),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_257)
      | k9_tmap_1('#skF_3',B_257) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_257,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_891])).

tff(c_928,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_26,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k7_tmap_1(A_56,B_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_56),u1_struct_0(k6_tmap_1(A_56,B_57)))))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_344,plain,(
    ! [A_185,B_186] :
      ( m1_subset_1(k7_tmap_1(A_185,u1_struct_0(B_186)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_185),u1_struct_0(k8_tmap_1(A_185,B_186)))))
      | ~ m1_subset_1(u1_struct_0(B_186),k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185)
      | ~ m1_pre_topc(B_186,A_185)
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_26])).

tff(c_358,plain,(
    ! [A_75,B_79] :
      ( m1_subset_1(k7_tmap_1(A_75,u1_struct_0(B_79)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75),u1_struct_0(A_75))))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75)
      | ~ m1_pre_topc(B_79,A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75)
      | ~ m1_pre_topc(B_79,A_75)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_344])).

tff(c_844,plain,(
    ! [B_257] :
      ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_257),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_257,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_257,'#skF_3')
      | v2_struct_0(B_257)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_257) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_257,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_358])).

tff(c_885,plain,(
    ! [B_257] :
      ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_257),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_257)
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_257) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_257,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_56,c_54,c_56,c_54,c_844])).

tff(c_886,plain,(
    ! [B_257] :
      ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_257),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_257)
      | k9_tmap_1('#skF_3',B_257) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_257,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_885])).

tff(c_948,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_886])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,F_8,D_6,C_5,E_7,B_4] :
      ( r1_funct_2(A_3,B_4,C_5,D_6,E_7,E_7)
      | ~ m1_subset_1(F_8,k1_zfmisc_1(k2_zfmisc_1(C_5,D_6)))
      | ~ v1_funct_2(F_8,C_5,D_6)
      | ~ v1_funct_1(F_8)
      | ~ m1_subset_1(E_7,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(E_7,A_3,B_4)
      | ~ v1_funct_1(E_7)
      | v1_xboole_0(D_6)
      | v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_952,plain,(
    ! [A_3,B_4,E_7] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),E_7,E_7)
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(E_7,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(E_7,A_3,B_4)
      | ~ v1_funct_1(E_7)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_4) ) ),
    inference(resolution,[status(thm)],[c_948,c_6])).

tff(c_959,plain,(
    ! [A_3,B_4,E_7] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),E_7,E_7)
      | ~ m1_subset_1(E_7,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(E_7,A_3,B_4)
      | ~ v1_funct_1(E_7)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_928,c_952])).

tff(c_960,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_959])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_963,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_960,c_4])).

tff(c_966,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_963])).

tff(c_969,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_966])).

tff(c_973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_969])).

tff(c_975,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_959])).

tff(c_974,plain,(
    ! [A_3,B_4,E_7] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),E_7,E_7)
      | ~ m1_subset_1(E_7,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(E_7,A_3,B_4)
      | ~ v1_funct_1(E_7)
      | v1_xboole_0(B_4) ) ),
    inference(splitRight,[status(thm)],[c_959])).

tff(c_577,plain,(
    ! [B_228] :
      ( '#skF_2'('#skF_3',B_228,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_228)
      | k9_tmap_1('#skF_3',B_228) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_228,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_575])).

tff(c_20,plain,(
    ! [A_34,B_46,C_52] :
      ( ~ r1_funct_2(u1_struct_0(A_34),u1_struct_0(k8_tmap_1(A_34,B_46)),u1_struct_0(A_34),u1_struct_0(k6_tmap_1(A_34,'#skF_2'(A_34,B_46,C_52))),C_52,k7_tmap_1(A_34,'#skF_2'(A_34,B_46,C_52)))
      | k9_tmap_1(A_34,B_46) = C_52
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34),u1_struct_0(k8_tmap_1(A_34,B_46)))))
      | ~ v1_funct_2(C_52,u1_struct_0(A_34),u1_struct_0(k8_tmap_1(A_34,B_46)))
      | ~ v1_funct_1(C_52)
      | ~ m1_pre_topc(B_46,A_34)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_583,plain,(
    ! [B_228] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_228)),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0(B_228))),k6_partfun1(u1_struct_0('#skF_3')),k7_tmap_1('#skF_3','#skF_2'('#skF_3',B_228,k6_partfun1(u1_struct_0('#skF_3')))))
      | k9_tmap_1('#skF_3',B_228) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_228)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_228)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_228,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_228) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_228,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_20])).

tff(c_592,plain,(
    ! [B_228] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_228)),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0(B_228))),k6_partfun1(u1_struct_0('#skF_3')),k7_tmap_1('#skF_3','#skF_2'('#skF_3',B_228,k6_partfun1(u1_struct_0('#skF_3')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_228)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_228)))
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_228) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_228,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_139,c_583])).

tff(c_598,plain,(
    ! [B_229] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_229)),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0(B_229))),k6_partfun1(u1_struct_0('#skF_3')),k7_tmap_1('#skF_3','#skF_2'('#skF_3',B_229,k6_partfun1(u1_struct_0('#skF_3')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_229)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_229)))
      | k9_tmap_1('#skF_3',B_229) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_229,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_592])).

tff(c_605,plain,(
    ! [B_59] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)),k6_partfun1(u1_struct_0('#skF_3')),k7_tmap_1('#skF_3','#skF_2'('#skF_3',B_59,k6_partfun1(u1_struct_0('#skF_3')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))
      | k9_tmap_1('#skF_3',B_59) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_598])).

tff(c_614,plain,(
    ! [B_59] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)),k6_partfun1(u1_struct_0('#skF_3')),k7_tmap_1('#skF_3','#skF_2'('#skF_3',B_59,k6_partfun1(u1_struct_0('#skF_3')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))
      | k9_tmap_1('#skF_3',B_59) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_605])).

tff(c_615,plain,(
    ! [B_59] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)),k6_partfun1(u1_struct_0('#skF_3')),k7_tmap_1('#skF_3','#skF_2'('#skF_3',B_59,k6_partfun1(u1_struct_0('#skF_3')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))
      | k9_tmap_1('#skF_3',B_59) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_59,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_614])).

tff(c_790,plain,(
    ! [B_256] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_256)),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_256)),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_256)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_256)))
      | k9_tmap_1('#skF_3',B_256) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_256,'#skF_3')
      | k9_tmap_1('#skF_3',B_256) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_256,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_615])).

tff(c_826,plain,(
    ! [B_256] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_256)),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_256)),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_256)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_256)))
      | k9_tmap_1('#skF_3',B_256) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_256,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_139,c_790])).

tff(c_3651,plain,(
    ! [B_492] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_492)),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_492)),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_492)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_492)))
      | k9_tmap_1('#skF_3',B_492) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_492,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_826])).

tff(c_3655,plain,(
    ! [B_79] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3651])).

tff(c_3661,plain,(
    ! [B_79] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3655])).

tff(c_3764,plain,(
    ! [B_521] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_521)),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_521)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_521)))
      | k9_tmap_1('#skF_3',B_521) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_521,'#skF_3')
      | v2_struct_0(B_521) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3661])).

tff(c_3768,plain,(
    ! [B_79] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3764])).

tff(c_3770,plain,(
    ! [B_79] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3768])).

tff(c_3771,plain,(
    ! [B_79] :
      ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3770])).

tff(c_3772,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3771])).

tff(c_3775,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_974,c_3772])).

tff(c_3778,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_928,c_948,c_3775])).

tff(c_3780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_975,c_3778])).

tff(c_3783,plain,(
    ! [B_522] :
      ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_522)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_522)))
      | k9_tmap_1('#skF_3',B_522) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_522,'#skF_3')
      | v2_struct_0(B_522) ) ),
    inference(splitRight,[status(thm)],[c_3771])).

tff(c_3797,plain,(
    ! [B_79] :
      ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3783])).

tff(c_3805,plain,(
    ! [B_79] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_79)))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_948,c_3797])).

tff(c_3807,plain,(
    ! [B_523] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_523)))
      | k9_tmap_1('#skF_3',B_523) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_523,'#skF_3')
      | v2_struct_0(B_523) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3805])).

tff(c_3821,plain,(
    ! [B_79] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_3807])).

tff(c_3829,plain,(
    ! [B_79] :
      ( k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_928,c_3821])).

tff(c_3865,plain,(
    ! [B_526] :
      ( k9_tmap_1('#skF_3',B_526) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_526,'#skF_3')
      | v2_struct_0(B_526) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3829])).

tff(c_3867,plain,
    ( k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_3865])).

tff(c_3870,plain,(
    k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3867])).

tff(c_325,plain,(
    ! [C_182,A_183,D_184] :
      ( r1_tmap_1(C_182,k6_tmap_1(A_183,u1_struct_0(C_182)),k2_tmap_1(A_183,k6_tmap_1(A_183,u1_struct_0(C_182)),k7_tmap_1(A_183,u1_struct_0(C_182)),C_182),D_184)
      | ~ m1_subset_1(D_184,u1_struct_0(C_182))
      | ~ m1_pre_topc(C_182,A_183)
      | v2_struct_0(C_182)
      | ~ m1_subset_1(u1_struct_0(C_182),k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_343,plain,(
    ! [B_84,A_82,D_184] :
      ( r1_tmap_1(B_84,k6_tmap_1(A_82,u1_struct_0(B_84)),k2_tmap_1(A_82,k6_tmap_1(A_82,u1_struct_0(B_84)),k6_partfun1(u1_struct_0(A_82)),B_84),D_184)
      | ~ m1_subset_1(D_184,u1_struct_0(B_84))
      | ~ m1_pre_topc(B_84,A_82)
      | v2_struct_0(B_84)
      | ~ m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_325])).

tff(c_3917,plain,(
    ! [B_84,D_184] :
      ( r1_tmap_1(B_84,k6_tmap_1('#skF_3',u1_struct_0(B_84)),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_84)),k9_tmap_1('#skF_3','#skF_4'),B_84),D_184)
      | ~ m1_subset_1(D_184,u1_struct_0(B_84))
      | ~ m1_pre_topc(B_84,'#skF_3')
      | v2_struct_0(B_84)
      | ~ m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3870,c_343])).

tff(c_3953,plain,(
    ! [B_84,D_184] :
      ( r1_tmap_1(B_84,k6_tmap_1('#skF_3',u1_struct_0(B_84)),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_84)),k9_tmap_1('#skF_3','#skF_4'),B_84),D_184)
      | ~ m1_subset_1(D_184,u1_struct_0(B_84))
      | v2_struct_0(B_84)
      | ~ m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_56,c_54,c_3917])).

tff(c_4895,plain,(
    ! [B_576,D_577] :
      ( r1_tmap_1(B_576,k6_tmap_1('#skF_3',u1_struct_0(B_576)),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_576)),k9_tmap_1('#skF_3','#skF_4'),B_576),D_577)
      | ~ m1_subset_1(D_577,u1_struct_0(B_576))
      | v2_struct_0(B_576)
      | ~ m1_subset_1(u1_struct_0(B_576),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_576,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3953])).

tff(c_4899,plain,(
    ! [B_59,D_577] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_59)),k9_tmap_1('#skF_3','#skF_4'),B_59),D_577)
      | ~ m1_subset_1(D_577,u1_struct_0(B_59))
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_4895])).

tff(c_4911,plain,(
    ! [B_59,D_577] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_59)),k9_tmap_1('#skF_3','#skF_4'),B_59),D_577)
      | ~ m1_subset_1(D_577,u1_struct_0(B_59))
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4899])).

tff(c_4916,plain,(
    ! [B_578,D_579] :
      ( r1_tmap_1(B_578,k8_tmap_1('#skF_3',B_578),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_578)),k9_tmap_1('#skF_3','#skF_4'),B_578),D_579)
      | ~ m1_subset_1(D_579,u1_struct_0(B_578))
      | v2_struct_0(B_578)
      | ~ m1_subset_1(u1_struct_0(B_578),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_578,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4911])).

tff(c_4920,plain,(
    ! [B_59,D_579] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_59),k9_tmap_1('#skF_3','#skF_4'),B_59),D_579)
      | ~ m1_subset_1(D_579,u1_struct_0(B_59))
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_4916])).

tff(c_4925,plain,(
    ! [B_59,D_579] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_59),k9_tmap_1('#skF_3','#skF_4'),B_59),D_579)
      | ~ m1_subset_1(D_579,u1_struct_0(B_59))
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4920])).

tff(c_4955,plain,(
    ! [B_583,D_584] :
      ( r1_tmap_1(B_583,k8_tmap_1('#skF_3',B_583),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_583),k9_tmap_1('#skF_3','#skF_4'),B_583),D_584)
      | ~ m1_subset_1(D_584,u1_struct_0(B_583))
      | v2_struct_0(B_583)
      | ~ m1_subset_1(u1_struct_0(B_583),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_583,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4925])).

tff(c_46,plain,(
    ~ r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_4958,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4955,c_46])).

tff(c_4961,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4958])).

tff(c_4962,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4961])).

tff(c_4965,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_4962])).

tff(c_4969,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_4965])).

tff(c_4999,plain,(
    ! [B_586] :
      ( ~ m1_subset_1(u1_struct_0(B_586),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_586)
      | k9_tmap_1('#skF_3',B_586) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_586,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_886])).

tff(c_5006,plain,(
    ! [B_84] :
      ( v2_struct_0(B_84)
      | k9_tmap_1('#skF_3',B_84) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_4999])).

tff(c_5010,plain,(
    ! [B_587] :
      ( v2_struct_0(B_587)
      | k9_tmap_1('#skF_3',B_587) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_587,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5006])).

tff(c_5012,plain,
    ( v2_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_5010])).

tff(c_5015,plain,(
    k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5012])).

tff(c_4971,plain,(
    ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_886])).

tff(c_5018,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5015,c_4971])).

tff(c_314,plain,(
    ! [A_58,B_59] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_58)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58),u1_struct_0(k8_tmap_1(A_58,B_59)))))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_309])).

tff(c_5043,plain,(
    ! [B_59] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5015,c_314])).

tff(c_5068,plain,(
    ! [B_59] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_54,c_56,c_56,c_54,c_5043])).

tff(c_5224,plain,(
    ! [B_594] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_594)))))
      | ~ m1_subset_1(u1_struct_0(B_594),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_594,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5068])).

tff(c_5236,plain,(
    ! [B_79] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5224])).

tff(c_5249,plain,(
    ! [B_79] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5236])).

tff(c_5273,plain,(
    ! [B_599] :
      ( ~ m1_subset_1(u1_struct_0(B_599),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_599,'#skF_3')
      | v2_struct_0(B_599) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5018,c_5249])).

tff(c_5280,plain,(
    ! [B_84] :
      ( v2_struct_0(B_84)
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_5273])).

tff(c_5284,plain,(
    ! [B_600] :
      ( v2_struct_0(B_600)
      | ~ m1_pre_topc(B_600,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5280])).

tff(c_5287,plain,(
    v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_5284])).

tff(c_5291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5287])).

tff(c_5302,plain,(
    ! [B_602] :
      ( ~ m1_subset_1(u1_struct_0(B_602),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_602)
      | k9_tmap_1('#skF_3',B_602) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_602,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_5309,plain,(
    ! [B_84] :
      ( v2_struct_0(B_84)
      | k9_tmap_1('#skF_3',B_84) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_5302])).

tff(c_5313,plain,(
    ! [B_603] :
      ( v2_struct_0(B_603)
      | k9_tmap_1('#skF_3',B_603) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_603,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5309])).

tff(c_5315,plain,
    ( v2_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_5313])).

tff(c_5318,plain,(
    k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5315])).

tff(c_5293,plain,(
    ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_5321,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5318,c_5293])).

tff(c_5346,plain,(
    ! [B_59] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5318,c_262])).

tff(c_5371,plain,(
    ! [B_59] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_54,c_56,c_56,c_54,c_5346])).

tff(c_5505,plain,(
    ! [B_608] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_608)))
      | ~ m1_subset_1(u1_struct_0(B_608),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_608,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5371])).

tff(c_5509,plain,(
    ! [B_79] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5505])).

tff(c_5511,plain,(
    ! [B_79] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5509])).

tff(c_5513,plain,(
    ! [B_609] :
      ( ~ m1_subset_1(u1_struct_0(B_609),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_609,'#skF_3')
      | v2_struct_0(B_609) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5321,c_5511])).

tff(c_5520,plain,(
    ! [B_84] :
      ( v2_struct_0(B_84)
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_44,c_5513])).

tff(c_5524,plain,(
    ! [B_610] :
      ( v2_struct_0(B_610)
      | ~ m1_pre_topc(B_610,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5520])).

tff(c_5527,plain,(
    v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_5524])).

tff(c_5531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.85/2.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.98/2.95  
% 8.98/2.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.98/2.95  %$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 8.98/2.95  
% 8.98/2.95  %Foreground sorts:
% 8.98/2.95  
% 8.98/2.95  
% 8.98/2.95  %Background operators:
% 8.98/2.95  
% 8.98/2.95  
% 8.98/2.95  %Foreground operators:
% 8.98/2.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.98/2.95  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 8.98/2.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.98/2.95  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.98/2.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.98/2.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.98/2.95  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 8.98/2.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.98/2.95  tff('#skF_5', type, '#skF_5': $i).
% 8.98/2.95  tff(k9_tmap_1, type, k9_tmap_1: ($i * $i) > $i).
% 8.98/2.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.98/2.95  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 8.98/2.95  tff('#skF_3', type, '#skF_3': $i).
% 8.98/2.95  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.98/2.95  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.98/2.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.98/2.95  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.98/2.95  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.98/2.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.98/2.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.98/2.95  tff('#skF_4', type, '#skF_4': $i).
% 8.98/2.95  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 8.98/2.95  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 8.98/2.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.98/2.95  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.98/2.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.98/2.95  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 8.98/2.95  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.98/2.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.98/2.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.98/2.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.98/2.95  
% 8.98/2.98  tff(f_222, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tmap_1(B, k8_tmap_1(A, B), k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_tmap_1)).
% 8.98/2.98  tff(f_203, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 8.98/2.98  tff(f_151, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 8.98/2.98  tff(f_95, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 8.98/2.98  tff(f_69, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_tmap_1(A, B) = k6_partfun1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 8.98/2.98  tff(f_136, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 8.98/2.98  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))) => ((C = k9_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => r1_funct_2(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, D)), C, k7_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_tmap_1)).
% 8.98/2.98  tff(f_196, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_tmap_1)).
% 8.98/2.98  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.98/2.98  tff(f_57, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 8.98/2.98  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 8.98/2.98  tff(f_174, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => ((u1_struct_0(C) = B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_tmap_1)).
% 8.98/2.98  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.98/2.98  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.98/2.98  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.98/2.98  tff(c_44, plain, (![B_84, A_82]: (m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_203])).
% 8.98/2.98  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.98/2.98  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.98/2.98  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.98/2.98  tff(c_32, plain, (![A_58, B_59]: (l1_pre_topc(k8_tmap_1(A_58, B_59)) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.98/2.98  tff(c_36, plain, (![A_58, B_59]: (v1_pre_topc(k8_tmap_1(A_58, B_59)) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.98/2.98  tff(c_34, plain, (![A_58, B_59]: (v2_pre_topc(k8_tmap_1(A_58, B_59)) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.98/2.98  tff(c_209, plain, (![A_145, B_146]: (k6_tmap_1(A_145, u1_struct_0(B_146))=k8_tmap_1(A_145, B_146) | ~m1_subset_1(u1_struct_0(B_146), k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(k8_tmap_1(A_145, B_146)) | ~v2_pre_topc(k8_tmap_1(A_145, B_146)) | ~v1_pre_topc(k8_tmap_1(A_145, B_146)) | ~m1_pre_topc(B_146, A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.98/2.98  tff(c_220, plain, (![A_147, B_148]: (k6_tmap_1(A_147, u1_struct_0(B_148))=k8_tmap_1(A_147, B_148) | ~l1_pre_topc(k8_tmap_1(A_147, B_148)) | ~v2_pre_topc(k8_tmap_1(A_147, B_148)) | ~v1_pre_topc(k8_tmap_1(A_147, B_148)) | ~v2_pre_topc(A_147) | v2_struct_0(A_147) | ~m1_pre_topc(B_148, A_147) | ~l1_pre_topc(A_147))), inference(resolution, [status(thm)], [c_44, c_209])).
% 8.98/2.98  tff(c_225, plain, (![A_149, B_150]: (k6_tmap_1(A_149, u1_struct_0(B_150))=k8_tmap_1(A_149, B_150) | ~l1_pre_topc(k8_tmap_1(A_149, B_150)) | ~v1_pre_topc(k8_tmap_1(A_149, B_150)) | ~m1_pre_topc(B_150, A_149) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(resolution, [status(thm)], [c_34, c_220])).
% 8.98/2.98  tff(c_230, plain, (![A_151, B_152]: (k6_tmap_1(A_151, u1_struct_0(B_152))=k8_tmap_1(A_151, B_152) | ~l1_pre_topc(k8_tmap_1(A_151, B_152)) | ~m1_pre_topc(B_152, A_151) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_36, c_225])).
% 8.98/2.98  tff(c_234, plain, (![A_58, B_59]: (k6_tmap_1(A_58, u1_struct_0(B_59))=k8_tmap_1(A_58, B_59) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_32, c_230])).
% 8.98/2.98  tff(c_71, plain, (![A_103, B_104]: (k7_tmap_1(A_103, B_104)=k6_partfun1(u1_struct_0(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.98/2.98  tff(c_76, plain, (![A_105, B_106]: (k7_tmap_1(A_105, u1_struct_0(B_106))=k6_partfun1(u1_struct_0(A_105)) | ~v2_pre_topc(A_105) | v2_struct_0(A_105) | ~m1_pre_topc(B_106, A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_44, c_71])).
% 8.98/2.98  tff(c_65, plain, (![A_99, B_100]: (v1_funct_1(k7_tmap_1(A_99, B_100)) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.98/2.98  tff(c_69, plain, (![A_82, B_84]: (v1_funct_1(k7_tmap_1(A_82, u1_struct_0(B_84))) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_44, c_65])).
% 8.98/2.98  tff(c_133, plain, (![A_115, B_116]: (v1_funct_1(k6_partfun1(u1_struct_0(A_115))) | ~v2_pre_topc(A_115) | v2_struct_0(A_115) | ~m1_pre_topc(B_116, A_115) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115) | ~m1_pre_topc(B_116, A_115) | ~l1_pre_topc(A_115))), inference(superposition, [status(thm), theory('equality')], [c_76, c_69])).
% 8.98/2.98  tff(c_135, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_133])).
% 8.98/2.98  tff(c_138, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_56, c_135])).
% 8.98/2.98  tff(c_139, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_138])).
% 8.98/2.98  tff(c_75, plain, (![A_82, B_84]: (k7_tmap_1(A_82, u1_struct_0(B_84))=k6_partfun1(u1_struct_0(A_82)) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_44, c_71])).
% 8.98/2.98  tff(c_118, plain, (![A_109, B_110]: (v1_funct_2(k7_tmap_1(A_109, B_110), u1_struct_0(A_109), u1_struct_0(k6_tmap_1(A_109, B_110))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.98/2.98  tff(c_259, plain, (![A_167, B_168]: (v1_funct_2(k6_partfun1(u1_struct_0(A_167)), u1_struct_0(A_167), u1_struct_0(k6_tmap_1(A_167, u1_struct_0(B_168)))) | ~m1_subset_1(u1_struct_0(B_168), k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167) | ~m1_pre_topc(B_168, A_167) | ~l1_pre_topc(A_167))), inference(superposition, [status(thm), theory('equality')], [c_75, c_118])).
% 8.98/2.98  tff(c_262, plain, (![A_58, B_59]: (v1_funct_2(k6_partfun1(u1_struct_0(A_58)), u1_struct_0(A_58), u1_struct_0(k8_tmap_1(A_58, B_59))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_234, c_259])).
% 8.98/2.98  tff(c_125, plain, (![A_111, B_112]: (m1_subset_1(k7_tmap_1(A_111, B_112), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(k6_tmap_1(A_111, B_112))))) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.98/2.98  tff(c_309, plain, (![A_180, B_181]: (m1_subset_1(k6_partfun1(u1_struct_0(A_180)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_180), u1_struct_0(k6_tmap_1(A_180, u1_struct_0(B_181)))))) | ~m1_subset_1(u1_struct_0(B_181), k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180) | ~m1_pre_topc(B_181, A_180) | ~l1_pre_topc(A_180))), inference(superposition, [status(thm), theory('equality')], [c_75, c_125])).
% 8.98/2.98  tff(c_500, plain, (![A_218, B_219]: (m1_subset_1(k6_partfun1(u1_struct_0(A_218)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_218), u1_struct_0(k8_tmap_1(A_218, B_219))))) | ~m1_subset_1(u1_struct_0(B_219), k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218) | ~m1_pre_topc(B_219, A_218) | ~l1_pre_topc(A_218) | ~m1_pre_topc(B_219, A_218) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(superposition, [status(thm), theory('equality')], [c_234, c_309])).
% 8.98/2.98  tff(c_22, plain, (![B_46, A_34, C_52]: (u1_struct_0(B_46)='#skF_2'(A_34, B_46, C_52) | k9_tmap_1(A_34, B_46)=C_52 | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))))) | ~v1_funct_2(C_52, u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))) | ~v1_funct_1(C_52) | ~m1_pre_topc(B_46, A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.98/2.98  tff(c_521, plain, (![A_220, B_221]: ('#skF_2'(A_220, B_221, k6_partfun1(u1_struct_0(A_220)))=u1_struct_0(B_221) | k9_tmap_1(A_220, B_221)=k6_partfun1(u1_struct_0(A_220)) | ~v1_funct_2(k6_partfun1(u1_struct_0(A_220)), u1_struct_0(A_220), u1_struct_0(k8_tmap_1(A_220, B_221))) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_220))) | ~m1_subset_1(u1_struct_0(B_221), k1_zfmisc_1(u1_struct_0(A_220))) | ~m1_pre_topc(B_221, A_220) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(resolution, [status(thm)], [c_500, c_22])).
% 8.98/2.98  tff(c_560, plain, (![A_224, B_225]: ('#skF_2'(A_224, B_225, k6_partfun1(u1_struct_0(A_224)))=u1_struct_0(B_225) | k9_tmap_1(A_224, B_225)=k6_partfun1(u1_struct_0(A_224)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_224))) | ~m1_subset_1(u1_struct_0(B_225), k1_zfmisc_1(u1_struct_0(A_224))) | ~m1_pre_topc(B_225, A_224) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224))), inference(resolution, [status(thm)], [c_262, c_521])).
% 8.98/2.98  tff(c_568, plain, (![A_226, B_227]: ('#skF_2'(A_226, B_227, k6_partfun1(u1_struct_0(A_226)))=u1_struct_0(B_227) | k9_tmap_1(A_226, B_227)=k6_partfun1(u1_struct_0(A_226)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_226))) | ~v2_pre_topc(A_226) | v2_struct_0(A_226) | ~m1_pre_topc(B_227, A_226) | ~l1_pre_topc(A_226))), inference(resolution, [status(thm)], [c_44, c_560])).
% 8.98/2.98  tff(c_570, plain, (![B_227]: ('#skF_2'('#skF_3', B_227, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_227) | k9_tmap_1('#skF_3', B_227)=k6_partfun1(u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_227, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_139, c_568])).
% 8.98/2.98  tff(c_575, plain, (![B_227]: ('#skF_2'('#skF_3', B_227, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_227) | k9_tmap_1('#skF_3', B_227)=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_227, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_570])).
% 8.98/2.98  tff(c_576, plain, (![B_227]: ('#skF_2'('#skF_3', B_227, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_227) | k9_tmap_1('#skF_3', B_227)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_227, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_575])).
% 8.98/2.98  tff(c_24, plain, (![A_34, B_46, C_52]: (m1_subset_1('#skF_2'(A_34, B_46, C_52), k1_zfmisc_1(u1_struct_0(A_34))) | k9_tmap_1(A_34, B_46)=C_52 | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))))) | ~v1_funct_2(C_52, u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))) | ~v1_funct_1(C_52) | ~m1_pre_topc(B_46, A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.98/2.98  tff(c_661, plain, (![A_239, B_240]: (m1_subset_1('#skF_2'(A_239, B_240, k6_partfun1(u1_struct_0(A_239))), k1_zfmisc_1(u1_struct_0(A_239))) | k9_tmap_1(A_239, B_240)=k6_partfun1(u1_struct_0(A_239)) | ~v1_funct_2(k6_partfun1(u1_struct_0(A_239)), u1_struct_0(A_239), u1_struct_0(k8_tmap_1(A_239, B_240))) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_239))) | ~m1_subset_1(u1_struct_0(B_240), k1_zfmisc_1(u1_struct_0(A_239))) | ~m1_pre_topc(B_240, A_239) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239))), inference(resolution, [status(thm)], [c_500, c_24])).
% 8.98/2.98  tff(c_697, plain, (![A_244, B_245]: (m1_subset_1('#skF_2'(A_244, B_245, k6_partfun1(u1_struct_0(A_244))), k1_zfmisc_1(u1_struct_0(A_244))) | k9_tmap_1(A_244, B_245)=k6_partfun1(u1_struct_0(A_244)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_244))) | ~m1_subset_1(u1_struct_0(B_245), k1_zfmisc_1(u1_struct_0(A_244))) | ~m1_pre_topc(B_245, A_244) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(resolution, [status(thm)], [c_262, c_661])).
% 8.98/2.98  tff(c_8, plain, (![A_9, B_11]: (k7_tmap_1(A_9, B_11)=k6_partfun1(u1_struct_0(A_9)) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.98/2.98  tff(c_775, plain, (![A_253, B_254]: (k7_tmap_1(A_253, '#skF_2'(A_253, B_254, k6_partfun1(u1_struct_0(A_253))))=k6_partfun1(u1_struct_0(A_253)) | k9_tmap_1(A_253, B_254)=k6_partfun1(u1_struct_0(A_253)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_253))) | ~m1_subset_1(u1_struct_0(B_254), k1_zfmisc_1(u1_struct_0(A_253))) | ~m1_pre_topc(B_254, A_253) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(resolution, [status(thm)], [c_697, c_8])).
% 8.98/2.98  tff(c_783, plain, (![A_255, B_256]: (k7_tmap_1(A_255, '#skF_2'(A_255, B_256, k6_partfun1(u1_struct_0(A_255))))=k6_partfun1(u1_struct_0(A_255)) | k9_tmap_1(A_255, B_256)=k6_partfun1(u1_struct_0(A_255)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_255))) | ~v2_pre_topc(A_255) | v2_struct_0(A_255) | ~m1_pre_topc(B_256, A_255) | ~l1_pre_topc(A_255))), inference(resolution, [status(thm)], [c_44, c_775])).
% 8.98/2.98  tff(c_820, plain, (![B_227]: (k7_tmap_1('#skF_3', u1_struct_0(B_227))=k6_partfun1(u1_struct_0('#skF_3')) | k9_tmap_1('#skF_3', B_227)=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_227, '#skF_3') | ~l1_pre_topc('#skF_3') | k9_tmap_1('#skF_3', B_227)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_227, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_576, c_783])).
% 8.98/2.98  tff(c_833, plain, (![B_227]: (k7_tmap_1('#skF_3', u1_struct_0(B_227))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_227)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_227, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_139, c_820])).
% 8.98/2.98  tff(c_835, plain, (![B_257]: (k7_tmap_1('#skF_3', u1_struct_0(B_257))=k6_partfun1(u1_struct_0('#skF_3')) | k9_tmap_1('#skF_3', B_257)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_257, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_833])).
% 8.98/2.98  tff(c_42, plain, (![A_75, B_79]: (u1_struct_0(k8_tmap_1(A_75, B_79))=u1_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | v2_struct_0(B_79) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.98/2.98  tff(c_239, plain, (![A_159, B_160]: (k6_tmap_1(A_159, u1_struct_0(B_160))=k8_tmap_1(A_159, B_160) | ~m1_pre_topc(B_160, A_159) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_32, c_230])).
% 8.98/2.98  tff(c_28, plain, (![A_56, B_57]: (v1_funct_2(k7_tmap_1(A_56, B_57), u1_struct_0(A_56), u1_struct_0(k6_tmap_1(A_56, B_57))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.98/2.98  tff(c_272, plain, (![A_169, B_170]: (v1_funct_2(k7_tmap_1(A_169, u1_struct_0(B_170)), u1_struct_0(A_169), u1_struct_0(k8_tmap_1(A_169, B_170))) | ~m1_subset_1(u1_struct_0(B_170), k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | ~m1_pre_topc(B_170, A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(superposition, [status(thm), theory('equality')], [c_239, c_28])).
% 8.98/2.98  tff(c_281, plain, (![A_75, B_79]: (v1_funct_2(k7_tmap_1(A_75, u1_struct_0(B_79)), u1_struct_0(A_75), u1_struct_0(A_75)) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | v2_struct_0(B_79) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_42, c_272])).
% 8.98/2.98  tff(c_850, plain, (![B_257]: (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_257), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_257, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_257, '#skF_3') | v2_struct_0(B_257) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_257)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_257, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_835, c_281])).
% 8.98/2.98  tff(c_891, plain, (![B_257]: (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_257), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_257) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_257)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_257, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_56, c_54, c_56, c_54, c_850])).
% 8.98/2.98  tff(c_892, plain, (![B_257]: (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_257), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_257) | k9_tmap_1('#skF_3', B_257)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_257, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_891])).
% 8.98/2.98  tff(c_928, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_892])).
% 8.98/2.98  tff(c_26, plain, (![A_56, B_57]: (m1_subset_1(k7_tmap_1(A_56, B_57), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_56), u1_struct_0(k6_tmap_1(A_56, B_57))))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.98/2.98  tff(c_344, plain, (![A_185, B_186]: (m1_subset_1(k7_tmap_1(A_185, u1_struct_0(B_186)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_185), u1_struct_0(k8_tmap_1(A_185, B_186))))) | ~m1_subset_1(u1_struct_0(B_186), k1_zfmisc_1(u1_struct_0(A_185))) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185) | ~m1_pre_topc(B_186, A_185) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185))), inference(superposition, [status(thm), theory('equality')], [c_239, c_26])).
% 8.98/2.98  tff(c_358, plain, (![A_75, B_79]: (m1_subset_1(k7_tmap_1(A_75, u1_struct_0(B_79)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75), u1_struct_0(A_75)))) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | v2_struct_0(B_79) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_42, c_344])).
% 8.98/2.98  tff(c_844, plain, (![B_257]: (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_257), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_257, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_257, '#skF_3') | v2_struct_0(B_257) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_257)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_257, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_835, c_358])).
% 8.98/2.98  tff(c_885, plain, (![B_257]: (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_257), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_257) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_257)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_257, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_56, c_54, c_56, c_54, c_844])).
% 8.98/2.98  tff(c_886, plain, (![B_257]: (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_257), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_257) | k9_tmap_1('#skF_3', B_257)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_257, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_885])).
% 8.98/2.98  tff(c_948, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_886])).
% 8.98/2.98  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.98/2.98  tff(c_6, plain, (![A_3, F_8, D_6, C_5, E_7, B_4]: (r1_funct_2(A_3, B_4, C_5, D_6, E_7, E_7) | ~m1_subset_1(F_8, k1_zfmisc_1(k2_zfmisc_1(C_5, D_6))) | ~v1_funct_2(F_8, C_5, D_6) | ~v1_funct_1(F_8) | ~m1_subset_1(E_7, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(E_7, A_3, B_4) | ~v1_funct_1(E_7) | v1_xboole_0(D_6) | v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.98/2.98  tff(c_952, plain, (![A_3, B_4, E_7]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), E_7, E_7) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(E_7, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(E_7, A_3, B_4) | ~v1_funct_1(E_7) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_4))), inference(resolution, [status(thm)], [c_948, c_6])).
% 8.98/2.98  tff(c_959, plain, (![A_3, B_4, E_7]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), E_7, E_7) | ~m1_subset_1(E_7, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(E_7, A_3, B_4) | ~v1_funct_1(E_7) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_928, c_952])).
% 8.98/2.98  tff(c_960, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_959])).
% 8.98/2.98  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.98/2.98  tff(c_963, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_960, c_4])).
% 8.98/2.98  tff(c_966, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_963])).
% 8.98/2.98  tff(c_969, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_966])).
% 8.98/2.98  tff(c_973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_969])).
% 8.98/2.98  tff(c_975, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_959])).
% 8.98/2.98  tff(c_974, plain, (![A_3, B_4, E_7]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), E_7, E_7) | ~m1_subset_1(E_7, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(E_7, A_3, B_4) | ~v1_funct_1(E_7) | v1_xboole_0(B_4))), inference(splitRight, [status(thm)], [c_959])).
% 8.98/2.98  tff(c_577, plain, (![B_228]: ('#skF_2'('#skF_3', B_228, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_228) | k9_tmap_1('#skF_3', B_228)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_228, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_575])).
% 8.98/2.98  tff(c_20, plain, (![A_34, B_46, C_52]: (~r1_funct_2(u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46)), u1_struct_0(A_34), u1_struct_0(k6_tmap_1(A_34, '#skF_2'(A_34, B_46, C_52))), C_52, k7_tmap_1(A_34, '#skF_2'(A_34, B_46, C_52))) | k9_tmap_1(A_34, B_46)=C_52 | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))))) | ~v1_funct_2(C_52, u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))) | ~v1_funct_1(C_52) | ~m1_pre_topc(B_46, A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.98/2.98  tff(c_583, plain, (![B_228]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_228)), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0(B_228))), k6_partfun1(u1_struct_0('#skF_3')), k7_tmap_1('#skF_3', '#skF_2'('#skF_3', B_228, k6_partfun1(u1_struct_0('#skF_3'))))) | k9_tmap_1('#skF_3', B_228)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_228))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_228))) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_228, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_228)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_228, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_577, c_20])).
% 8.98/2.98  tff(c_592, plain, (![B_228]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_228)), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0(B_228))), k6_partfun1(u1_struct_0('#skF_3')), k7_tmap_1('#skF_3', '#skF_2'('#skF_3', B_228, k6_partfun1(u1_struct_0('#skF_3'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_228))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_228))) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_228)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_228, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_139, c_583])).
% 8.98/2.98  tff(c_598, plain, (![B_229]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_229)), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0(B_229))), k6_partfun1(u1_struct_0('#skF_3')), k7_tmap_1('#skF_3', '#skF_2'('#skF_3', B_229, k6_partfun1(u1_struct_0('#skF_3'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_229))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_229))) | k9_tmap_1('#skF_3', B_229)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_229, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_592])).
% 8.98/2.98  tff(c_605, plain, (![B_59]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59)), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59)), k6_partfun1(u1_struct_0('#skF_3')), k7_tmap_1('#skF_3', '#skF_2'('#skF_3', B_59, k6_partfun1(u1_struct_0('#skF_3'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))) | k9_tmap_1('#skF_3', B_59)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_598])).
% 8.98/2.98  tff(c_614, plain, (![B_59]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59)), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59)), k6_partfun1(u1_struct_0('#skF_3')), k7_tmap_1('#skF_3', '#skF_2'('#skF_3', B_59, k6_partfun1(u1_struct_0('#skF_3'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))) | k9_tmap_1('#skF_3', B_59)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_605])).
% 8.98/2.98  tff(c_615, plain, (![B_59]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59)), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59)), k6_partfun1(u1_struct_0('#skF_3')), k7_tmap_1('#skF_3', '#skF_2'('#skF_3', B_59, k6_partfun1(u1_struct_0('#skF_3'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))) | k9_tmap_1('#skF_3', B_59)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_59, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_614])).
% 8.98/2.98  tff(c_790, plain, (![B_256]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_256)), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_256)), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_256))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_256))) | k9_tmap_1('#skF_3', B_256)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_256, '#skF_3') | k9_tmap_1('#skF_3', B_256)=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_256, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_783, c_615])).
% 8.98/2.98  tff(c_826, plain, (![B_256]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_256)), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_256)), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_256))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_256))) | k9_tmap_1('#skF_3', B_256)=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_256, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_139, c_790])).
% 8.98/2.98  tff(c_3651, plain, (![B_492]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_492)), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_492)), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_492))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_492))) | k9_tmap_1('#skF_3', B_492)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_492, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_826])).
% 8.98/2.98  tff(c_3655, plain, (![B_79]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79)), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3651])).
% 8.98/2.98  tff(c_3661, plain, (![B_79]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79)), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3655])).
% 8.98/2.98  tff(c_3764, plain, (![B_521]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_521)), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_521))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_521))) | k9_tmap_1('#skF_3', B_521)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_521, '#skF_3') | v2_struct_0(B_521))), inference(negUnitSimplification, [status(thm)], [c_58, c_3661])).
% 8.98/2.98  tff(c_3768, plain, (![B_79]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3764])).
% 8.98/2.98  tff(c_3770, plain, (![B_79]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3768])).
% 8.98/2.98  tff(c_3771, plain, (![B_79]: (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79))), inference(negUnitSimplification, [status(thm)], [c_58, c_3770])).
% 8.98/2.98  tff(c_3772, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_3771])).
% 8.98/2.98  tff(c_3775, plain, (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_974, c_3772])).
% 8.98/2.98  tff(c_3778, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_928, c_948, c_3775])).
% 8.98/2.98  tff(c_3780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_975, c_3778])).
% 8.98/2.98  tff(c_3783, plain, (![B_522]: (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_522))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_522))) | k9_tmap_1('#skF_3', B_522)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_522, '#skF_3') | v2_struct_0(B_522))), inference(splitRight, [status(thm)], [c_3771])).
% 8.98/2.98  tff(c_3797, plain, (![B_79]: (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3783])).
% 8.98/2.99  tff(c_3805, plain, (![B_79]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_79))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_948, c_3797])).
% 8.98/2.99  tff(c_3807, plain, (![B_523]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_523))) | k9_tmap_1('#skF_3', B_523)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_523, '#skF_3') | v2_struct_0(B_523))), inference(negUnitSimplification, [status(thm)], [c_58, c_3805])).
% 8.98/2.99  tff(c_3821, plain, (![B_79]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_3807])).
% 8.98/2.99  tff(c_3829, plain, (![B_79]: (k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_928, c_3821])).
% 8.98/2.99  tff(c_3865, plain, (![B_526]: (k9_tmap_1('#skF_3', B_526)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_526, '#skF_3') | v2_struct_0(B_526))), inference(negUnitSimplification, [status(thm)], [c_58, c_3829])).
% 8.98/2.99  tff(c_3867, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_3865])).
% 8.98/2.99  tff(c_3870, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_3867])).
% 8.98/2.99  tff(c_325, plain, (![C_182, A_183, D_184]: (r1_tmap_1(C_182, k6_tmap_1(A_183, u1_struct_0(C_182)), k2_tmap_1(A_183, k6_tmap_1(A_183, u1_struct_0(C_182)), k7_tmap_1(A_183, u1_struct_0(C_182)), C_182), D_184) | ~m1_subset_1(D_184, u1_struct_0(C_182)) | ~m1_pre_topc(C_182, A_183) | v2_struct_0(C_182) | ~m1_subset_1(u1_struct_0(C_182), k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_174])).
% 8.98/2.99  tff(c_343, plain, (![B_84, A_82, D_184]: (r1_tmap_1(B_84, k6_tmap_1(A_82, u1_struct_0(B_84)), k2_tmap_1(A_82, k6_tmap_1(A_82, u1_struct_0(B_84)), k6_partfun1(u1_struct_0(A_82)), B_84), D_184) | ~m1_subset_1(D_184, u1_struct_0(B_84)) | ~m1_pre_topc(B_84, A_82) | v2_struct_0(B_84) | ~m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_75, c_325])).
% 8.98/2.99  tff(c_3917, plain, (![B_84, D_184]: (r1_tmap_1(B_84, k6_tmap_1('#skF_3', u1_struct_0(B_84)), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_84)), k9_tmap_1('#skF_3', '#skF_4'), B_84), D_184) | ~m1_subset_1(D_184, u1_struct_0(B_84)) | ~m1_pre_topc(B_84, '#skF_3') | v2_struct_0(B_84) | ~m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3870, c_343])).
% 8.98/2.99  tff(c_3953, plain, (![B_84, D_184]: (r1_tmap_1(B_84, k6_tmap_1('#skF_3', u1_struct_0(B_84)), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_84)), k9_tmap_1('#skF_3', '#skF_4'), B_84), D_184) | ~m1_subset_1(D_184, u1_struct_0(B_84)) | v2_struct_0(B_84) | ~m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_56, c_54, c_3917])).
% 8.98/2.99  tff(c_4895, plain, (![B_576, D_577]: (r1_tmap_1(B_576, k6_tmap_1('#skF_3', u1_struct_0(B_576)), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_576)), k9_tmap_1('#skF_3', '#skF_4'), B_576), D_577) | ~m1_subset_1(D_577, u1_struct_0(B_576)) | v2_struct_0(B_576) | ~m1_subset_1(u1_struct_0(B_576), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_576, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_3953])).
% 8.98/2.99  tff(c_4899, plain, (![B_59, D_577]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_59)), k9_tmap_1('#skF_3', '#skF_4'), B_59), D_577) | ~m1_subset_1(D_577, u1_struct_0(B_59)) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_4895])).
% 8.98/2.99  tff(c_4911, plain, (![B_59, D_577]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_59)), k9_tmap_1('#skF_3', '#skF_4'), B_59), D_577) | ~m1_subset_1(D_577, u1_struct_0(B_59)) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4899])).
% 8.98/2.99  tff(c_4916, plain, (![B_578, D_579]: (r1_tmap_1(B_578, k8_tmap_1('#skF_3', B_578), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_578)), k9_tmap_1('#skF_3', '#skF_4'), B_578), D_579) | ~m1_subset_1(D_579, u1_struct_0(B_578)) | v2_struct_0(B_578) | ~m1_subset_1(u1_struct_0(B_578), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_578, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_4911])).
% 8.98/2.99  tff(c_4920, plain, (![B_59, D_579]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_59), k9_tmap_1('#skF_3', '#skF_4'), B_59), D_579) | ~m1_subset_1(D_579, u1_struct_0(B_59)) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_234, c_4916])).
% 8.98/2.99  tff(c_4925, plain, (![B_59, D_579]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_59), k9_tmap_1('#skF_3', '#skF_4'), B_59), D_579) | ~m1_subset_1(D_579, u1_struct_0(B_59)) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_4920])).
% 8.98/2.99  tff(c_4955, plain, (![B_583, D_584]: (r1_tmap_1(B_583, k8_tmap_1('#skF_3', B_583), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_583), k9_tmap_1('#skF_3', '#skF_4'), B_583), D_584) | ~m1_subset_1(D_584, u1_struct_0(B_583)) | v2_struct_0(B_583) | ~m1_subset_1(u1_struct_0(B_583), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_583, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_4925])).
% 8.98/2.99  tff(c_46, plain, (~r1_tmap_1('#skF_4', k8_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', '#skF_4'), k9_tmap_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.98/2.99  tff(c_4958, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4955, c_46])).
% 8.98/2.99  tff(c_4961, plain, (v2_struct_0('#skF_4') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4958])).
% 8.98/2.99  tff(c_4962, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_4961])).
% 8.98/2.99  tff(c_4965, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_4962])).
% 8.98/2.99  tff(c_4969, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_4965])).
% 8.98/2.99  tff(c_4999, plain, (![B_586]: (~m1_subset_1(u1_struct_0(B_586), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_586) | k9_tmap_1('#skF_3', B_586)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_586, '#skF_3'))), inference(splitRight, [status(thm)], [c_886])).
% 8.98/2.99  tff(c_5006, plain, (![B_84]: (v2_struct_0(B_84) | k9_tmap_1('#skF_3', B_84)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_4999])).
% 8.98/2.99  tff(c_5010, plain, (![B_587]: (v2_struct_0(B_587) | k9_tmap_1('#skF_3', B_587)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_587, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5006])).
% 8.98/2.99  tff(c_5012, plain, (v2_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_5010])).
% 8.98/2.99  tff(c_5015, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_5012])).
% 8.98/2.99  tff(c_4971, plain, (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_886])).
% 8.98/2.99  tff(c_5018, plain, (~m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_5015, c_4971])).
% 8.98/2.99  tff(c_314, plain, (![A_58, B_59]: (m1_subset_1(k6_partfun1(u1_struct_0(A_58)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58), u1_struct_0(k8_tmap_1(A_58, B_59))))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_234, c_309])).
% 8.98/2.99  tff(c_5043, plain, (![B_59]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5015, c_314])).
% 8.98/2.99  tff(c_5068, plain, (![B_59]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_54, c_56, c_56, c_54, c_5043])).
% 8.98/2.99  tff(c_5224, plain, (![B_594]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_594))))) | ~m1_subset_1(u1_struct_0(B_594), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_594, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_5068])).
% 8.98/2.99  tff(c_5236, plain, (![B_79]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_79, '#skF_3') | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5224])).
% 8.98/2.99  tff(c_5249, plain, (![B_79]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_5236])).
% 8.98/2.99  tff(c_5273, plain, (![B_599]: (~m1_subset_1(u1_struct_0(B_599), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_599, '#skF_3') | v2_struct_0(B_599))), inference(negUnitSimplification, [status(thm)], [c_58, c_5018, c_5249])).
% 8.98/2.99  tff(c_5280, plain, (![B_84]: (v2_struct_0(B_84) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_5273])).
% 8.98/2.99  tff(c_5284, plain, (![B_600]: (v2_struct_0(B_600) | ~m1_pre_topc(B_600, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5280])).
% 8.98/2.99  tff(c_5287, plain, (v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_5284])).
% 8.98/2.99  tff(c_5291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_5287])).
% 8.98/2.99  tff(c_5302, plain, (![B_602]: (~m1_subset_1(u1_struct_0(B_602), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_602) | k9_tmap_1('#skF_3', B_602)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_602, '#skF_3'))), inference(splitRight, [status(thm)], [c_892])).
% 8.98/2.99  tff(c_5309, plain, (![B_84]: (v2_struct_0(B_84) | k9_tmap_1('#skF_3', B_84)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_5302])).
% 8.98/2.99  tff(c_5313, plain, (![B_603]: (v2_struct_0(B_603) | k9_tmap_1('#skF_3', B_603)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_603, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5309])).
% 8.98/2.99  tff(c_5315, plain, (v2_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_5313])).
% 8.98/2.99  tff(c_5318, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_5315])).
% 8.98/2.99  tff(c_5293, plain, (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_892])).
% 8.98/2.99  tff(c_5321, plain, (~v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5318, c_5293])).
% 8.98/2.99  tff(c_5346, plain, (![B_59]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5318, c_262])).
% 8.98/2.99  tff(c_5371, plain, (![B_59]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_54, c_56, c_56, c_54, c_5346])).
% 8.98/2.99  tff(c_5505, plain, (![B_608]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_608))) | ~m1_subset_1(u1_struct_0(B_608), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_608, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_5371])).
% 8.98/2.99  tff(c_5509, plain, (![B_79]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_79, '#skF_3') | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5505])).
% 8.98/2.99  tff(c_5511, plain, (![B_79]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_5509])).
% 8.98/2.99  tff(c_5513, plain, (![B_609]: (~m1_subset_1(u1_struct_0(B_609), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_609, '#skF_3') | v2_struct_0(B_609))), inference(negUnitSimplification, [status(thm)], [c_58, c_5321, c_5511])).
% 8.98/2.99  tff(c_5520, plain, (![B_84]: (v2_struct_0(B_84) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_5513])).
% 8.98/2.99  tff(c_5524, plain, (![B_610]: (v2_struct_0(B_610) | ~m1_pre_topc(B_610, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5520])).
% 8.98/2.99  tff(c_5527, plain, (v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_5524])).
% 8.98/2.99  tff(c_5531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_5527])).
% 8.98/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.98/2.99  
% 8.98/2.99  Inference rules
% 8.98/2.99  ----------------------
% 8.98/2.99  #Ref     : 0
% 8.98/2.99  #Sup     : 1138
% 8.98/2.99  #Fact    : 0
% 8.98/2.99  #Define  : 0
% 8.98/2.99  #Split   : 7
% 8.98/2.99  #Chain   : 0
% 8.98/2.99  #Close   : 0
% 8.98/2.99  
% 8.98/2.99  Ordering : KBO
% 8.98/2.99  
% 8.98/2.99  Simplification rules
% 8.98/2.99  ----------------------
% 8.98/2.99  #Subsume      : 328
% 8.98/2.99  #Demod        : 1458
% 8.98/2.99  #Tautology    : 173
% 8.98/2.99  #SimpNegUnit  : 410
% 8.98/2.99  #BackRed      : 79
% 8.98/2.99  
% 8.98/2.99  #Partial instantiations: 0
% 8.98/2.99  #Strategies tried      : 1
% 8.98/2.99  
% 8.98/2.99  Timing (in seconds)
% 8.98/2.99  ----------------------
% 8.98/2.99  Preprocessing        : 0.45
% 8.98/2.99  Parsing              : 0.24
% 8.98/2.99  CNF conversion       : 0.03
% 8.98/2.99  Main loop            : 1.75
% 8.98/2.99  Inferencing          : 0.67
% 8.98/2.99  Reduction            : 0.49
% 8.98/2.99  Demodulation         : 0.33
% 8.98/2.99  BG Simplification    : 0.08
% 8.98/2.99  Subsumption          : 0.41
% 8.98/2.99  Abstraction          : 0.10
% 8.98/2.99  MUC search           : 0.00
% 8.98/2.99  Cooper               : 0.00
% 8.98/2.99  Total                : 2.26
% 8.98/2.99  Index Insertion      : 0.00
% 8.98/2.99  Index Deletion       : 0.00
% 8.98/2.99  Index Matching       : 0.00
% 8.98/2.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
