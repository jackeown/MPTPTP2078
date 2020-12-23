%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:01 EST 2020

% Result     : Theorem 35.36s
% Output     : CNFRefutation 35.70s
% Verified   : 
% Statistics : Number of formulae       :  318 (39465 expanded)
%              Number of leaves         :   43 (13836 expanded)
%              Depth                    :   67
%              Number of atoms          : 1647 (221994 expanded)
%              Number of equality atoms :  284 (21250 expanded)
%              Maximal formula depth    :   20 (   7 average)
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

tff(f_224,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_tmap_1)).

tff(f_205,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_153,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_97,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_123,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

tff(f_198,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_176,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_56,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_46,plain,(
    ! [B_84,A_82] :
      ( m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_58,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_34,plain,(
    ! [A_58,B_59] :
      ( l1_pre_topc(k8_tmap_1(A_58,B_59))
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_38,plain,(
    ! [A_58,B_59] :
      ( v1_pre_topc(k8_tmap_1(A_58,B_59))
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_36,plain,(
    ! [A_58,B_59] :
      ( v2_pre_topc(k8_tmap_1(A_58,B_59))
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_226,plain,(
    ! [A_155,B_156] :
      ( k6_tmap_1(A_155,u1_struct_0(B_156)) = k8_tmap_1(A_155,B_156)
      | ~ m1_subset_1(u1_struct_0(B_156),k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(k8_tmap_1(A_155,B_156))
      | ~ v2_pre_topc(k8_tmap_1(A_155,B_156))
      | ~ v1_pre_topc(k8_tmap_1(A_155,B_156))
      | ~ m1_pre_topc(B_156,A_155)
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_238,plain,(
    ! [A_163,B_164] :
      ( k6_tmap_1(A_163,u1_struct_0(B_164)) = k8_tmap_1(A_163,B_164)
      | ~ l1_pre_topc(k8_tmap_1(A_163,B_164))
      | ~ v2_pre_topc(k8_tmap_1(A_163,B_164))
      | ~ v1_pre_topc(k8_tmap_1(A_163,B_164))
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163)
      | ~ m1_pre_topc(B_164,A_163)
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_46,c_226])).

tff(c_243,plain,(
    ! [A_165,B_166] :
      ( k6_tmap_1(A_165,u1_struct_0(B_166)) = k8_tmap_1(A_165,B_166)
      | ~ l1_pre_topc(k8_tmap_1(A_165,B_166))
      | ~ v1_pre_topc(k8_tmap_1(A_165,B_166))
      | ~ m1_pre_topc(B_166,A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_36,c_238])).

tff(c_248,plain,(
    ! [A_167,B_168] :
      ( k6_tmap_1(A_167,u1_struct_0(B_168)) = k8_tmap_1(A_167,B_168)
      | ~ l1_pre_topc(k8_tmap_1(A_167,B_168))
      | ~ m1_pre_topc(B_168,A_167)
      | ~ l1_pre_topc(A_167)
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_38,c_243])).

tff(c_252,plain,(
    ! [A_58,B_59] :
      ( k6_tmap_1(A_58,u1_struct_0(B_59)) = k8_tmap_1(A_58,B_59)
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_34,c_248])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_103,B_104] :
      ( k7_tmap_1(A_103,B_104) = k6_partfun1(u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,(
    ! [A_105,B_106] :
      ( k7_tmap_1(A_105,u1_struct_0(B_106)) = k6_partfun1(u1_struct_0(A_105))
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105)
      | ~ m1_pre_topc(B_106,A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_67,plain,(
    ! [A_99,B_100] :
      ( v1_funct_1(k7_tmap_1(A_99,B_100))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_71,plain,(
    ! [A_82,B_84] :
      ( v1_funct_1(k7_tmap_1(A_82,u1_struct_0(B_84)))
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_46,c_67])).

tff(c_135,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_78,c_71])).

tff(c_137,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_135])).

tff(c_140,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_58,c_137])).

tff(c_141,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_140])).

tff(c_253,plain,(
    ! [A_169,B_170] :
      ( k6_tmap_1(A_169,u1_struct_0(B_170)) = k8_tmap_1(A_169,B_170)
      | ~ m1_pre_topc(B_170,A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_34,c_248])).

tff(c_77,plain,(
    ! [A_82,B_84] :
      ( k7_tmap_1(A_82,u1_struct_0(B_84)) = k6_partfun1(u1_struct_0(A_82))
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_120,plain,(
    ! [A_109,B_110] :
      ( v1_funct_2(k7_tmap_1(A_109,B_110),u1_struct_0(A_109),u1_struct_0(k6_tmap_1(A_109,B_110)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_126,plain,(
    ! [A_82,B_84] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_82)),u1_struct_0(A_82),u1_struct_0(k6_tmap_1(A_82,u1_struct_0(B_84))))
      | ~ m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_120])).

tff(c_259,plain,(
    ! [A_169,B_170] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_169)),u1_struct_0(A_169),u1_struct_0(k8_tmap_1(A_169,B_170)))
      | ~ m1_subset_1(u1_struct_0(B_170),k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169)
      | ~ m1_pre_topc(B_170,A_169)
      | ~ l1_pre_topc(A_169)
      | ~ m1_pre_topc(B_170,A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_126])).

tff(c_127,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k7_tmap_1(A_111,B_112),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111),u1_struct_0(k6_tmap_1(A_111,B_112)))))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_331,plain,(
    ! [A_188,B_189] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_188)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),u1_struct_0(k6_tmap_1(A_188,u1_struct_0(B_189))))))
      | ~ m1_subset_1(u1_struct_0(B_189),k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188)
      | ~ m1_pre_topc(B_189,A_188)
      | ~ l1_pre_topc(A_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_127])).

tff(c_503,plain,(
    ! [A_223,B_224] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_223)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_223),u1_struct_0(k8_tmap_1(A_223,B_224)))))
      | ~ m1_subset_1(u1_struct_0(B_224),k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223)
      | ~ m1_pre_topc(B_224,A_223)
      | ~ l1_pre_topc(A_223)
      | ~ m1_pre_topc(B_224,A_223)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_331])).

tff(c_24,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_552,plain,(
    ! [A_227,B_228] :
      ( '#skF_2'(A_227,B_228,k6_partfun1(u1_struct_0(A_227))) = u1_struct_0(B_228)
      | k9_tmap_1(A_227,B_228) = k6_partfun1(u1_struct_0(A_227))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_227)),u1_struct_0(A_227),u1_struct_0(k8_tmap_1(A_227,B_228)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_227)))
      | ~ m1_subset_1(u1_struct_0(B_228),k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ m1_pre_topc(B_228,A_227)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_503,c_24])).

tff(c_566,plain,(
    ! [A_229,B_230] :
      ( '#skF_2'(A_229,B_230,k6_partfun1(u1_struct_0(A_229))) = u1_struct_0(B_230)
      | k9_tmap_1(A_229,B_230) = k6_partfun1(u1_struct_0(A_229))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_229)))
      | ~ m1_subset_1(u1_struct_0(B_230),k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ m1_pre_topc(B_230,A_229)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_259,c_552])).

tff(c_574,plain,(
    ! [A_231,B_232] :
      ( '#skF_2'(A_231,B_232,k6_partfun1(u1_struct_0(A_231))) = u1_struct_0(B_232)
      | k9_tmap_1(A_231,B_232) = k6_partfun1(u1_struct_0(A_231))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_231)))
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231)
      | ~ m1_pre_topc(B_232,A_231)
      | ~ l1_pre_topc(A_231) ) ),
    inference(resolution,[status(thm)],[c_46,c_566])).

tff(c_576,plain,(
    ! [B_232] :
      ( '#skF_2'('#skF_3',B_232,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_232)
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_232,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_141,c_574])).

tff(c_581,plain,(
    ! [B_232] :
      ( '#skF_2'('#skF_3',B_232,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_232)
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_576])).

tff(c_582,plain,(
    ! [B_232] :
      ( '#skF_2'('#skF_3',B_232,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_232)
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_581])).

tff(c_26,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_646,plain,(
    ! [A_243,B_244] :
      ( m1_subset_1('#skF_2'(A_243,B_244,k6_partfun1(u1_struct_0(A_243))),k1_zfmisc_1(u1_struct_0(A_243)))
      | k9_tmap_1(A_243,B_244) = k6_partfun1(u1_struct_0(A_243))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_243)),u1_struct_0(A_243),u1_struct_0(k8_tmap_1(A_243,B_244)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_243)))
      | ~ m1_subset_1(u1_struct_0(B_244),k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ m1_pre_topc(B_244,A_243)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(resolution,[status(thm)],[c_503,c_26])).

tff(c_682,plain,(
    ! [A_248,B_249] :
      ( m1_subset_1('#skF_2'(A_248,B_249,k6_partfun1(u1_struct_0(A_248))),k1_zfmisc_1(u1_struct_0(A_248)))
      | k9_tmap_1(A_248,B_249) = k6_partfun1(u1_struct_0(A_248))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_248)))
      | ~ m1_subset_1(u1_struct_0(B_249),k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ m1_pre_topc(B_249,A_248)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(resolution,[status(thm)],[c_259,c_646])).

tff(c_10,plain,(
    ! [A_9,B_11] :
      ( k7_tmap_1(A_9,B_11) = k6_partfun1(u1_struct_0(A_9))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_763,plain,(
    ! [A_257,B_258] :
      ( k7_tmap_1(A_257,'#skF_2'(A_257,B_258,k6_partfun1(u1_struct_0(A_257)))) = k6_partfun1(u1_struct_0(A_257))
      | k9_tmap_1(A_257,B_258) = k6_partfun1(u1_struct_0(A_257))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_257)))
      | ~ m1_subset_1(u1_struct_0(B_258),k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ m1_pre_topc(B_258,A_257)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_682,c_10])).

tff(c_771,plain,(
    ! [A_259,B_260] :
      ( k7_tmap_1(A_259,'#skF_2'(A_259,B_260,k6_partfun1(u1_struct_0(A_259)))) = k6_partfun1(u1_struct_0(A_259))
      | k9_tmap_1(A_259,B_260) = k6_partfun1(u1_struct_0(A_259))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_259)))
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259)
      | ~ m1_pre_topc(B_260,A_259)
      | ~ l1_pre_topc(A_259) ) ),
    inference(resolution,[status(thm)],[c_46,c_763])).

tff(c_800,plain,(
    ! [B_232] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_232)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_232,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_771])).

tff(c_807,plain,(
    ! [B_232] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_232)) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_141,c_800])).

tff(c_809,plain,(
    ! [B_261] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_261)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k9_tmap_1('#skF_3',B_261) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_261,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_807])).

tff(c_44,plain,(
    ! [A_75,B_79] :
      ( u1_struct_0(k8_tmap_1(A_75,B_79)) = u1_struct_0(A_75)
      | ~ m1_pre_topc(B_79,A_75)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_30,plain,(
    ! [A_56,B_57] :
      ( v1_funct_2(k7_tmap_1(A_56,B_57),u1_struct_0(A_56),u1_struct_0(k6_tmap_1(A_56,B_57)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_294,plain,(
    ! [A_177,B_178] :
      ( v1_funct_2(k7_tmap_1(A_177,u1_struct_0(B_178)),u1_struct_0(A_177),u1_struct_0(k8_tmap_1(A_177,B_178)))
      | ~ m1_subset_1(u1_struct_0(B_178),k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177)
      | ~ m1_pre_topc(B_178,A_177)
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_30])).

tff(c_303,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_44,c_294])).

tff(c_827,plain,(
    ! [B_261] :
      ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_261),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_261,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_261,'#skF_3')
      | v2_struct_0(B_261)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_261) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_261,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_303])).

tff(c_868,plain,(
    ! [B_261] :
      ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_261),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_261)
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_261) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_261,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_58,c_56,c_58,c_56,c_827])).

tff(c_869,plain,(
    ! [B_261] :
      ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_261),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_261)
      | k9_tmap_1('#skF_3',B_261) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_261,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_868])).

tff(c_897,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_869])).

tff(c_28,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k7_tmap_1(A_56,B_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_56),u1_struct_0(k6_tmap_1(A_56,B_57)))))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_347,plain,(
    ! [A_190,B_191] :
      ( m1_subset_1(k7_tmap_1(A_190,u1_struct_0(B_191)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190),u1_struct_0(k8_tmap_1(A_190,B_191)))))
      | ~ m1_subset_1(u1_struct_0(B_191),k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190)
      | ~ m1_pre_topc(B_191,A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_28])).

tff(c_361,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_44,c_347])).

tff(c_821,plain,(
    ! [B_261] :
      ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_261),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_261,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_261,'#skF_3')
      | v2_struct_0(B_261)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_261) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_261,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_809,c_361])).

tff(c_862,plain,(
    ! [B_261] :
      ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_261),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_261)
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_261) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_261,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_58,c_56,c_58,c_56,c_821])).

tff(c_863,plain,(
    ! [B_261] :
      ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_261),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_261)
      | k9_tmap_1('#skF_3',B_261) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_261,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_862])).

tff(c_917,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_863])).

tff(c_6,plain,(
    ! [A_3,F_8,D_6,C_5,B_4] :
      ( r1_funct_2(A_3,B_4,C_5,D_6,F_8,F_8)
      | ~ m1_subset_1(F_8,k1_zfmisc_1(k2_zfmisc_1(C_5,D_6)))
      | ~ v1_funct_2(F_8,C_5,D_6)
      | ~ m1_subset_1(F_8,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(F_8,A_3,B_4)
      | ~ v1_funct_1(F_8)
      | v1_xboole_0(D_6)
      | v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_919,plain,(
    ! [A_3,B_4] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),A_3,B_4)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_4) ) ),
    inference(resolution,[status(thm)],[c_917,c_6])).

tff(c_922,plain,(
    ! [A_3,B_4] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),A_3,B_4)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_897,c_919])).

tff(c_981,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_922])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_984,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_981,c_4])).

tff(c_987,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_984])).

tff(c_990,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_987])).

tff(c_994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_990])).

tff(c_996,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_922])).

tff(c_808,plain,(
    ! [B_232] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_232)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_807])).

tff(c_324,plain,(
    ! [B_185,A_186,C_187] :
      ( u1_struct_0(B_185) = '#skF_2'(A_186,B_185,C_187)
      | k9_tmap_1(A_186,B_185) = C_187
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_186),u1_struct_0(k8_tmap_1(A_186,B_185)))))
      | ~ v1_funct_2(C_187,u1_struct_0(A_186),u1_struct_0(k8_tmap_1(A_186,B_185)))
      | ~ v1_funct_1(C_187)
      | ~ m1_pre_topc(B_185,A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_967,plain,(
    ! [B_268,A_269,C_270] :
      ( u1_struct_0(B_268) = '#skF_2'(A_269,B_268,C_270)
      | k9_tmap_1(A_269,B_268) = C_270
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_269),u1_struct_0(A_269))))
      | ~ v1_funct_2(C_270,u1_struct_0(A_269),u1_struct_0(k8_tmap_1(A_269,B_268)))
      | ~ v1_funct_1(C_270)
      | ~ m1_pre_topc(B_268,A_269)
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269)
      | ~ m1_pre_topc(B_268,A_269)
      | v2_struct_0(B_268)
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_324])).

tff(c_6275,plain,(
    ! [A_634,B_635,B_636] :
      ( '#skF_2'(A_634,B_635,k7_tmap_1(A_634,u1_struct_0(B_636))) = u1_struct_0(B_635)
      | k9_tmap_1(A_634,B_635) = k7_tmap_1(A_634,u1_struct_0(B_636))
      | ~ v1_funct_2(k7_tmap_1(A_634,u1_struct_0(B_636)),u1_struct_0(A_634),u1_struct_0(k8_tmap_1(A_634,B_635)))
      | ~ v1_funct_1(k7_tmap_1(A_634,u1_struct_0(B_636)))
      | ~ m1_pre_topc(B_635,A_634)
      | v2_struct_0(B_635)
      | ~ m1_subset_1(u1_struct_0(B_636),k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ m1_pre_topc(B_636,A_634)
      | v2_struct_0(B_636)
      | ~ l1_pre_topc(A_634)
      | ~ v2_pre_topc(A_634)
      | v2_struct_0(A_634) ) ),
    inference(resolution,[status(thm)],[c_361,c_967])).

tff(c_6290,plain,(
    ! [B_635,B_232] :
      ( '#skF_2'('#skF_3',B_635,k7_tmap_1('#skF_3',u1_struct_0(B_232))) = u1_struct_0(B_635)
      | k9_tmap_1('#skF_3',B_635) = k7_tmap_1('#skF_3',u1_struct_0(B_232))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_635)))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_232)))
      | ~ m1_pre_topc(B_635,'#skF_3')
      | v2_struct_0(B_635)
      | ~ m1_subset_1(u1_struct_0(B_232),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_232,'#skF_3')
      | v2_struct_0(B_232)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_6275])).

tff(c_6317,plain,(
    ! [B_635,B_232] :
      ( '#skF_2'('#skF_3',B_635,k7_tmap_1('#skF_3',u1_struct_0(B_232))) = u1_struct_0(B_635)
      | k9_tmap_1('#skF_3',B_635) = k7_tmap_1('#skF_3',u1_struct_0(B_232))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_635)))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_232)))
      | ~ m1_pre_topc(B_635,'#skF_3')
      | v2_struct_0(B_635)
      | ~ m1_subset_1(u1_struct_0(B_232),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_232)
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_6290])).

tff(c_6320,plain,(
    ! [B_637,B_638] :
      ( '#skF_2'('#skF_3',B_637,k7_tmap_1('#skF_3',u1_struct_0(B_638))) = u1_struct_0(B_637)
      | k9_tmap_1('#skF_3',B_637) = k7_tmap_1('#skF_3',u1_struct_0(B_638))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_637)))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_638)))
      | ~ m1_pre_topc(B_637,'#skF_3')
      | v2_struct_0(B_637)
      | ~ m1_subset_1(u1_struct_0(B_638),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_638)
      | k9_tmap_1('#skF_3',B_638) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_638,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6317])).

tff(c_6332,plain,(
    ! [B_79,B_638] :
      ( '#skF_2'('#skF_3',B_79,k7_tmap_1('#skF_3',u1_struct_0(B_638))) = u1_struct_0(B_79)
      | k9_tmap_1('#skF_3',B_79) = k7_tmap_1('#skF_3',u1_struct_0(B_638))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_638)))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ m1_subset_1(u1_struct_0(B_638),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_638)
      | k9_tmap_1('#skF_3',B_638) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_638,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_6320])).

tff(c_6341,plain,(
    ! [B_79,B_638] :
      ( '#skF_2'('#skF_3',B_79,k7_tmap_1('#skF_3',u1_struct_0(B_638))) = u1_struct_0(B_79)
      | k9_tmap_1('#skF_3',B_79) = k7_tmap_1('#skF_3',u1_struct_0(B_638))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_638)))
      | ~ m1_subset_1(u1_struct_0(B_638),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_638)
      | k9_tmap_1('#skF_3',B_638) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_638,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_897,c_6332])).

tff(c_6343,plain,(
    ! [B_639,B_640] :
      ( '#skF_2'('#skF_3',B_639,k7_tmap_1('#skF_3',u1_struct_0(B_640))) = u1_struct_0(B_639)
      | k9_tmap_1('#skF_3',B_639) = k7_tmap_1('#skF_3',u1_struct_0(B_640))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_640)))
      | ~ m1_subset_1(u1_struct_0(B_640),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_640)
      | k9_tmap_1('#skF_3',B_640) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_640,'#skF_3')
      | ~ m1_pre_topc(B_639,'#skF_3')
      | v2_struct_0(B_639) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6341])).

tff(c_6352,plain,(
    ! [B_639,B_84] :
      ( '#skF_2'('#skF_3',B_639,k7_tmap_1('#skF_3',u1_struct_0(B_84))) = u1_struct_0(B_639)
      | k9_tmap_1('#skF_3',B_639) = k7_tmap_1('#skF_3',u1_struct_0(B_84))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_84)))
      | v2_struct_0(B_84)
      | k9_tmap_1('#skF_3',B_84) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_639,'#skF_3')
      | v2_struct_0(B_639)
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_6343])).

tff(c_6395,plain,(
    ! [B_644,B_645] :
      ( '#skF_2'('#skF_3',B_644,k7_tmap_1('#skF_3',u1_struct_0(B_645))) = u1_struct_0(B_644)
      | k9_tmap_1('#skF_3',B_644) = k7_tmap_1('#skF_3',u1_struct_0(B_645))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_645)))
      | v2_struct_0(B_645)
      | k9_tmap_1('#skF_3',B_645) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_644,'#skF_3')
      | v2_struct_0(B_644)
      | ~ m1_pre_topc(B_645,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6352])).

tff(c_6401,plain,(
    ! [B_644,B_232] :
      ( '#skF_2'('#skF_3',B_644,k7_tmap_1('#skF_3',u1_struct_0(B_232))) = u1_struct_0(B_644)
      | k9_tmap_1('#skF_3',B_644) = k7_tmap_1('#skF_3',u1_struct_0(B_232))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_232)
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_644,'#skF_3')
      | v2_struct_0(B_644)
      | ~ m1_pre_topc(B_232,'#skF_3')
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_6395])).

tff(c_6424,plain,(
    ! [B_646,B_647] :
      ( '#skF_2'('#skF_3',B_646,k7_tmap_1('#skF_3',u1_struct_0(B_647))) = u1_struct_0(B_646)
      | k9_tmap_1('#skF_3',B_646) = k7_tmap_1('#skF_3',u1_struct_0(B_647))
      | v2_struct_0(B_647)
      | ~ m1_pre_topc(B_646,'#skF_3')
      | v2_struct_0(B_646)
      | k9_tmap_1('#skF_3',B_647) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_647,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_6401])).

tff(c_6532,plain,(
    ! [B_646,B_84] :
      ( '#skF_2'('#skF_3',B_646,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_646)
      | k9_tmap_1('#skF_3',B_646) = k7_tmap_1('#skF_3',u1_struct_0(B_84))
      | v2_struct_0(B_84)
      | ~ m1_pre_topc(B_646,'#skF_3')
      | v2_struct_0(B_646)
      | k9_tmap_1('#skF_3',B_84) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_6424])).

tff(c_6577,plain,(
    ! [B_646,B_84] :
      ( '#skF_2'('#skF_3',B_646,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_646)
      | k9_tmap_1('#skF_3',B_646) = k7_tmap_1('#skF_3',u1_struct_0(B_84))
      | v2_struct_0(B_84)
      | ~ m1_pre_topc(B_646,'#skF_3')
      | v2_struct_0(B_646)
      | k9_tmap_1('#skF_3',B_84) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_6532])).

tff(c_6580,plain,(
    ! [B_648,B_649] :
      ( '#skF_2'('#skF_3',B_648,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_648)
      | k9_tmap_1('#skF_3',B_648) = k7_tmap_1('#skF_3',u1_struct_0(B_649))
      | v2_struct_0(B_649)
      | ~ m1_pre_topc(B_648,'#skF_3')
      | v2_struct_0(B_648)
      | k9_tmap_1('#skF_3',B_649) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_649,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6577])).

tff(c_265,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_253,c_30])).

tff(c_2784,plain,(
    ! [A_439,B_440] :
      ( '#skF_2'(A_439,B_440,k7_tmap_1(A_439,u1_struct_0(B_440))) = u1_struct_0(B_440)
      | k7_tmap_1(A_439,u1_struct_0(B_440)) = k9_tmap_1(A_439,B_440)
      | ~ v1_funct_2(k7_tmap_1(A_439,u1_struct_0(B_440)),u1_struct_0(A_439),u1_struct_0(k8_tmap_1(A_439,B_440)))
      | ~ v1_funct_1(k7_tmap_1(A_439,u1_struct_0(B_440)))
      | ~ m1_subset_1(u1_struct_0(B_440),k1_zfmisc_1(u1_struct_0(A_439)))
      | ~ m1_pre_topc(B_440,A_439)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439)
      | v2_struct_0(A_439) ) ),
    inference(resolution,[status(thm)],[c_347,c_24])).

tff(c_2813,plain,(
    ! [A_441,B_442] :
      ( '#skF_2'(A_441,B_442,k7_tmap_1(A_441,u1_struct_0(B_442))) = u1_struct_0(B_442)
      | k7_tmap_1(A_441,u1_struct_0(B_442)) = k9_tmap_1(A_441,B_442)
      | ~ v1_funct_1(k7_tmap_1(A_441,u1_struct_0(B_442)))
      | ~ m1_subset_1(u1_struct_0(B_442),k1_zfmisc_1(u1_struct_0(A_441)))
      | ~ m1_pre_topc(B_442,A_441)
      | ~ l1_pre_topc(A_441)
      | ~ v2_pre_topc(A_441)
      | v2_struct_0(A_441) ) ),
    inference(resolution,[status(thm)],[c_265,c_2784])).

tff(c_2884,plain,(
    ! [A_445,B_446] :
      ( '#skF_2'(A_445,B_446,k7_tmap_1(A_445,u1_struct_0(B_446))) = u1_struct_0(B_446)
      | k7_tmap_1(A_445,u1_struct_0(B_446)) = k9_tmap_1(A_445,B_446)
      | ~ v1_funct_1(k7_tmap_1(A_445,u1_struct_0(B_446)))
      | ~ v2_pre_topc(A_445)
      | v2_struct_0(A_445)
      | ~ m1_pre_topc(B_446,A_445)
      | ~ l1_pre_topc(A_445) ) ),
    inference(resolution,[status(thm)],[c_46,c_2813])).

tff(c_2912,plain,(
    ! [A_82,B_84] :
      ( '#skF_2'(A_82,B_84,k7_tmap_1(A_82,u1_struct_0(B_84))) = u1_struct_0(B_84)
      | k7_tmap_1(A_82,u1_struct_0(B_84)) = k9_tmap_1(A_82,B_84)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_71,c_2884])).

tff(c_6779,plain,(
    ! [B_649,B_648] :
      ( '#skF_2'('#skF_3',B_649,k9_tmap_1('#skF_3',B_648)) = u1_struct_0(B_649)
      | k7_tmap_1('#skF_3',u1_struct_0(B_649)) = k9_tmap_1('#skF_3',B_649)
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_649,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | '#skF_2'('#skF_3',B_648,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_648)
      | v2_struct_0(B_649)
      | ~ m1_pre_topc(B_648,'#skF_3')
      | v2_struct_0(B_648)
      | k9_tmap_1('#skF_3',B_649) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_649,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6580,c_2912])).

tff(c_6967,plain,(
    ! [B_649,B_648] :
      ( '#skF_2'('#skF_3',B_649,k9_tmap_1('#skF_3',B_648)) = u1_struct_0(B_649)
      | k7_tmap_1('#skF_3',u1_struct_0(B_649)) = k9_tmap_1('#skF_3',B_649)
      | v2_struct_0('#skF_3')
      | '#skF_2'('#skF_3',B_648,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_648)
      | v2_struct_0(B_649)
      | ~ m1_pre_topc(B_648,'#skF_3')
      | v2_struct_0(B_648)
      | k9_tmap_1('#skF_3',B_649) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_649,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_6779])).

tff(c_10271,plain,(
    ! [B_805,B_806] :
      ( '#skF_2'('#skF_3',B_805,k9_tmap_1('#skF_3',B_806)) = u1_struct_0(B_805)
      | k7_tmap_1('#skF_3',u1_struct_0(B_805)) = k9_tmap_1('#skF_3',B_805)
      | '#skF_2'('#skF_3',B_806,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_806)
      | v2_struct_0(B_805)
      | ~ m1_pre_topc(B_806,'#skF_3')
      | v2_struct_0(B_806)
      | k9_tmap_1('#skF_3',B_805) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_805,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6967])).

tff(c_10426,plain,(
    ! [B_805,B_806] :
      ( k9_tmap_1('#skF_3',B_805) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_805,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | '#skF_2'('#skF_3',B_805,k9_tmap_1('#skF_3',B_806)) = u1_struct_0(B_805)
      | '#skF_2'('#skF_3',B_806,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_806)
      | v2_struct_0(B_805)
      | ~ m1_pre_topc(B_806,'#skF_3')
      | v2_struct_0(B_806)
      | k9_tmap_1('#skF_3',B_805) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_805,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10271,c_77])).

tff(c_10672,plain,(
    ! [B_805,B_806] :
      ( v2_struct_0('#skF_3')
      | '#skF_2'('#skF_3',B_805,k9_tmap_1('#skF_3',B_806)) = u1_struct_0(B_805)
      | '#skF_2'('#skF_3',B_806,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_806)
      | v2_struct_0(B_805)
      | ~ m1_pre_topc(B_806,'#skF_3')
      | v2_struct_0(B_806)
      | k9_tmap_1('#skF_3',B_805) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_805,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_10426])).

tff(c_10741,plain,(
    ! [B_807,B_808] :
      ( '#skF_2'('#skF_3',B_807,k9_tmap_1('#skF_3',B_808)) = u1_struct_0(B_807)
      | '#skF_2'('#skF_3',B_808,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_808)
      | v2_struct_0(B_807)
      | ~ m1_pre_topc(B_808,'#skF_3')
      | v2_struct_0(B_808)
      | k9_tmap_1('#skF_3',B_807) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_807,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_10672])).

tff(c_2972,plain,(
    ! [A_450,B_451] :
      ( '#skF_2'(A_450,B_451,k7_tmap_1(A_450,u1_struct_0(B_451))) = u1_struct_0(B_451)
      | k7_tmap_1(A_450,u1_struct_0(B_451)) = k9_tmap_1(A_450,B_451)
      | ~ v2_pre_topc(A_450)
      | v2_struct_0(A_450)
      | ~ m1_pre_topc(B_451,A_450)
      | ~ l1_pre_topc(A_450) ) ),
    inference(resolution,[status(thm)],[c_71,c_2884])).

tff(c_3012,plain,(
    ! [A_82,B_84] :
      ( '#skF_2'(A_82,B_84,k6_partfun1(u1_struct_0(A_82))) = u1_struct_0(B_84)
      | k7_tmap_1(A_82,u1_struct_0(B_84)) = k9_tmap_1(A_82,B_84)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_2972])).

tff(c_10925,plain,(
    ! [B_84,B_807,B_808] :
      ( '#skF_2'('#skF_3',B_84,k9_tmap_1('#skF_3',B_807)) = u1_struct_0(B_84)
      | k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k9_tmap_1('#skF_3',B_84)
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | '#skF_2'('#skF_3',B_807,k9_tmap_1('#skF_3',B_808)) = u1_struct_0(B_807)
      | '#skF_2'('#skF_3',B_808,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_808)
      | v2_struct_0(B_807)
      | ~ m1_pre_topc(B_808,'#skF_3')
      | v2_struct_0(B_808)
      | ~ m1_pre_topc(B_807,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10741,c_3012])).

tff(c_11121,plain,(
    ! [B_84,B_807,B_808] :
      ( '#skF_2'('#skF_3',B_84,k9_tmap_1('#skF_3',B_807)) = u1_struct_0(B_84)
      | k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k9_tmap_1('#skF_3',B_84)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3')
      | '#skF_2'('#skF_3',B_807,k9_tmap_1('#skF_3',B_808)) = u1_struct_0(B_807)
      | '#skF_2'('#skF_3',B_808,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_808)
      | v2_struct_0(B_807)
      | ~ m1_pre_topc(B_808,'#skF_3')
      | v2_struct_0(B_808)
      | ~ m1_pre_topc(B_807,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_56,c_58,c_10925])).

tff(c_11122,plain,(
    ! [B_84,B_807,B_808] :
      ( '#skF_2'('#skF_3',B_84,k9_tmap_1('#skF_3',B_807)) = u1_struct_0(B_84)
      | k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k9_tmap_1('#skF_3',B_84)
      | ~ m1_pre_topc(B_84,'#skF_3')
      | '#skF_2'('#skF_3',B_807,k9_tmap_1('#skF_3',B_808)) = u1_struct_0(B_807)
      | '#skF_2'('#skF_3',B_808,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_808)
      | v2_struct_0(B_807)
      | ~ m1_pre_topc(B_808,'#skF_3')
      | v2_struct_0(B_808)
      | ~ m1_pre_topc(B_807,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11121])).

tff(c_33324,plain,(
    ! [B_1090] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_1090)) = k9_tmap_1('#skF_3',B_1090)
      | '#skF_2'('#skF_3',B_1090,k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0(B_1090)
      | v2_struct_0(B_1090)
      | ~ m1_pre_topc(B_1090,'#skF_3')
      | '#skF_2'('#skF_3',B_1090,k9_tmap_1('#skF_3',B_1090)) = u1_struct_0(B_1090) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_11122])).

tff(c_262,plain,(
    ! [A_169,B_170] :
      ( m1_subset_1(k7_tmap_1(A_169,u1_struct_0(B_170)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_169),u1_struct_0(k8_tmap_1(A_169,B_170)))))
      | ~ m1_subset_1(u1_struct_0(B_170),k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169)
      | ~ m1_pre_topc(B_170,A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_28])).

tff(c_427,plain,(
    ! [A_201,B_202,C_203] :
      ( m1_subset_1('#skF_2'(A_201,B_202,C_203),k1_zfmisc_1(u1_struct_0(A_201)))
      | k9_tmap_1(A_201,B_202) = C_203
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_201),u1_struct_0(k8_tmap_1(A_201,B_202)))))
      | ~ v1_funct_2(C_203,u1_struct_0(A_201),u1_struct_0(k8_tmap_1(A_201,B_202)))
      | ~ v1_funct_1(C_203)
      | ~ m1_pre_topc(B_202,A_201)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4089,plain,(
    ! [A_523,B_524] :
      ( m1_subset_1('#skF_2'(A_523,B_524,k7_tmap_1(A_523,u1_struct_0(B_524))),k1_zfmisc_1(u1_struct_0(A_523)))
      | k7_tmap_1(A_523,u1_struct_0(B_524)) = k9_tmap_1(A_523,B_524)
      | ~ v1_funct_2(k7_tmap_1(A_523,u1_struct_0(B_524)),u1_struct_0(A_523),u1_struct_0(k8_tmap_1(A_523,B_524)))
      | ~ v1_funct_1(k7_tmap_1(A_523,u1_struct_0(B_524)))
      | ~ m1_subset_1(u1_struct_0(B_524),k1_zfmisc_1(u1_struct_0(A_523)))
      | ~ m1_pre_topc(B_524,A_523)
      | ~ l1_pre_topc(A_523)
      | ~ v2_pre_topc(A_523)
      | v2_struct_0(A_523) ) ),
    inference(resolution,[status(thm)],[c_262,c_427])).

tff(c_4121,plain,(
    ! [A_525,B_526] :
      ( m1_subset_1('#skF_2'(A_525,B_526,k7_tmap_1(A_525,u1_struct_0(B_526))),k1_zfmisc_1(u1_struct_0(A_525)))
      | k7_tmap_1(A_525,u1_struct_0(B_526)) = k9_tmap_1(A_525,B_526)
      | ~ v1_funct_1(k7_tmap_1(A_525,u1_struct_0(B_526)))
      | ~ m1_subset_1(u1_struct_0(B_526),k1_zfmisc_1(u1_struct_0(A_525)))
      | ~ m1_pre_topc(B_526,A_525)
      | ~ l1_pre_topc(A_525)
      | ~ v2_pre_topc(A_525)
      | v2_struct_0(A_525) ) ),
    inference(resolution,[status(thm)],[c_265,c_4089])).

tff(c_4206,plain,(
    ! [A_533,B_534] :
      ( k7_tmap_1(A_533,'#skF_2'(A_533,B_534,k7_tmap_1(A_533,u1_struct_0(B_534)))) = k6_partfun1(u1_struct_0(A_533))
      | k7_tmap_1(A_533,u1_struct_0(B_534)) = k9_tmap_1(A_533,B_534)
      | ~ v1_funct_1(k7_tmap_1(A_533,u1_struct_0(B_534)))
      | ~ m1_subset_1(u1_struct_0(B_534),k1_zfmisc_1(u1_struct_0(A_533)))
      | ~ m1_pre_topc(B_534,A_533)
      | ~ l1_pre_topc(A_533)
      | ~ v2_pre_topc(A_533)
      | v2_struct_0(A_533) ) ),
    inference(resolution,[status(thm)],[c_4121,c_10])).

tff(c_4226,plain,(
    ! [A_535,B_536] :
      ( k7_tmap_1(A_535,'#skF_2'(A_535,B_536,k7_tmap_1(A_535,u1_struct_0(B_536)))) = k6_partfun1(u1_struct_0(A_535))
      | k7_tmap_1(A_535,u1_struct_0(B_536)) = k9_tmap_1(A_535,B_536)
      | ~ v1_funct_1(k7_tmap_1(A_535,u1_struct_0(B_536)))
      | ~ v2_pre_topc(A_535)
      | v2_struct_0(A_535)
      | ~ m1_pre_topc(B_536,A_535)
      | ~ l1_pre_topc(A_535) ) ),
    inference(resolution,[status(thm)],[c_46,c_4206])).

tff(c_4285,plain,(
    ! [A_82,B_84] :
      ( k7_tmap_1(A_82,'#skF_2'(A_82,B_84,k6_partfun1(u1_struct_0(A_82)))) = k6_partfun1(u1_struct_0(A_82))
      | k7_tmap_1(A_82,u1_struct_0(B_84)) = k9_tmap_1(A_82,B_84)
      | ~ v1_funct_1(k7_tmap_1(A_82,u1_struct_0(B_84)))
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82)
      | ~ m1_pre_topc(B_84,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_4226])).

tff(c_33378,plain,(
    ! [B_1090] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_1090)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k7_tmap_1('#skF_3',u1_struct_0(B_1090)) = k9_tmap_1('#skF_3',B_1090)
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_1090)))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1090,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1090,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | k7_tmap_1('#skF_3',u1_struct_0(B_1090)) = k9_tmap_1('#skF_3',B_1090)
      | v2_struct_0(B_1090)
      | ~ m1_pre_topc(B_1090,'#skF_3')
      | '#skF_2'('#skF_3',B_1090,k9_tmap_1('#skF_3',B_1090)) = u1_struct_0(B_1090) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33324,c_4285])).

tff(c_33718,plain,(
    ! [B_1090] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_1090)) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_1090)))
      | v2_struct_0('#skF_3')
      | k7_tmap_1('#skF_3',u1_struct_0(B_1090)) = k9_tmap_1('#skF_3',B_1090)
      | v2_struct_0(B_1090)
      | ~ m1_pre_topc(B_1090,'#skF_3')
      | '#skF_2'('#skF_3',B_1090,k9_tmap_1('#skF_3',B_1090)) = u1_struct_0(B_1090) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_56,c_58,c_33378])).

tff(c_33834,plain,(
    ! [B_1095] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_1095)) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k7_tmap_1('#skF_3',u1_struct_0(B_1095)))
      | k7_tmap_1('#skF_3',u1_struct_0(B_1095)) = k9_tmap_1('#skF_3',B_1095)
      | v2_struct_0(B_1095)
      | ~ m1_pre_topc(B_1095,'#skF_3')
      | '#skF_2'('#skF_3',B_1095,k9_tmap_1('#skF_3',B_1095)) = u1_struct_0(B_1095) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_33718])).

tff(c_33897,plain,(
    ! [B_84] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k9_tmap_1('#skF_3',B_84)
      | v2_struct_0(B_84)
      | ~ m1_pre_topc(B_84,'#skF_3')
      | '#skF_2'('#skF_3',B_84,k9_tmap_1('#skF_3',B_84)) = u1_struct_0(B_84)
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_33834])).

tff(c_33927,plain,(
    ! [B_84] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k9_tmap_1('#skF_3',B_84)
      | v2_struct_0(B_84)
      | '#skF_2'('#skF_3',B_84,k9_tmap_1('#skF_3',B_84)) = u1_struct_0(B_84)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_141,c_33897])).

tff(c_33928,plain,(
    ! [B_84] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k7_tmap_1('#skF_3',u1_struct_0(B_84)) = k9_tmap_1('#skF_3',B_84)
      | v2_struct_0(B_84)
      | '#skF_2'('#skF_3',B_84,k9_tmap_1('#skF_3',B_84)) = u1_struct_0(B_84)
      | ~ m1_pre_topc(B_84,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_33927])).

tff(c_35644,plain,(
    ! [B_1098] :
      ( v2_struct_0(B_1098)
      | '#skF_2'('#skF_3',B_1098,k9_tmap_1('#skF_3',B_1098)) = u1_struct_0(B_1098)
      | ~ m1_pre_topc(B_1098,'#skF_3')
      | k7_tmap_1('#skF_3',u1_struct_0(B_1098)) = k9_tmap_1('#skF_3',B_1098)
      | k9_tmap_1('#skF_3',B_1098) != k6_partfun1(u1_struct_0('#skF_3')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_33928])).

tff(c_275,plain,(
    ! [C_174,A_175,D_176] :
      ( r1_tmap_1(C_174,k6_tmap_1(A_175,u1_struct_0(C_174)),k2_tmap_1(A_175,k6_tmap_1(A_175,u1_struct_0(C_174)),k7_tmap_1(A_175,u1_struct_0(C_174)),C_174),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(C_174))
      | ~ m1_pre_topc(C_174,A_175)
      | v2_struct_0(C_174)
      | ~ m1_subset_1(u1_struct_0(C_174),k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_281,plain,(
    ! [B_59,A_58,D_176] :
      ( r1_tmap_1(B_59,k6_tmap_1(A_58,u1_struct_0(B_59)),k2_tmap_1(A_58,k8_tmap_1(A_58,B_59),k7_tmap_1(A_58,u1_struct_0(B_59)),B_59),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(B_59))
      | ~ m1_pre_topc(B_59,A_58)
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_275])).

tff(c_35903,plain,(
    ! [B_1098,D_176] :
      ( r1_tmap_1(B_1098,k6_tmap_1('#skF_3',u1_struct_0(B_1098)),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_1098),k9_tmap_1('#skF_3',B_1098),B_1098),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(B_1098))
      | ~ m1_pre_topc(B_1098,'#skF_3')
      | v2_struct_0(B_1098)
      | ~ m1_subset_1(u1_struct_0(B_1098),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1098,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | v2_struct_0(B_1098)
      | '#skF_2'('#skF_3',B_1098,k9_tmap_1('#skF_3',B_1098)) = u1_struct_0(B_1098)
      | ~ m1_pre_topc(B_1098,'#skF_3')
      | k9_tmap_1('#skF_3',B_1098) != k6_partfun1(u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35644,c_281])).

tff(c_36251,plain,(
    ! [B_1098,D_176] :
      ( r1_tmap_1(B_1098,k6_tmap_1('#skF_3',u1_struct_0(B_1098)),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_1098),k9_tmap_1('#skF_3',B_1098),B_1098),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(B_1098))
      | ~ m1_subset_1(u1_struct_0(B_1098),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | v2_struct_0(B_1098)
      | '#skF_2'('#skF_3',B_1098,k9_tmap_1('#skF_3',B_1098)) = u1_struct_0(B_1098)
      | ~ m1_pre_topc(B_1098,'#skF_3')
      | k9_tmap_1('#skF_3',B_1098) != k6_partfun1(u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_58,c_56,c_35903])).

tff(c_51979,plain,(
    ! [B_1178,D_1179] :
      ( r1_tmap_1(B_1178,k6_tmap_1('#skF_3',u1_struct_0(B_1178)),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_1178),k9_tmap_1('#skF_3',B_1178),B_1178),D_1179)
      | ~ m1_subset_1(D_1179,u1_struct_0(B_1178))
      | ~ m1_subset_1(u1_struct_0(B_1178),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_1178)
      | '#skF_2'('#skF_3',B_1178,k9_tmap_1('#skF_3',B_1178)) = u1_struct_0(B_1178)
      | ~ m1_pre_topc(B_1178,'#skF_3')
      | k9_tmap_1('#skF_3',B_1178) != k6_partfun1(u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_36251])).

tff(c_52016,plain,(
    ! [B_59,D_1179] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_59),k9_tmap_1('#skF_3',B_59),B_59),D_1179)
      | ~ m1_subset_1(D_1179,u1_struct_0(B_59))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_59)
      | '#skF_2'('#skF_3',B_59,k9_tmap_1('#skF_3',B_59)) = u1_struct_0(B_59)
      | ~ m1_pre_topc(B_59,'#skF_3')
      | k9_tmap_1('#skF_3',B_59) != k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_51979])).

tff(c_52021,plain,(
    ! [B_59,D_1179] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_59),k9_tmap_1('#skF_3',B_59),B_59),D_1179)
      | ~ m1_subset_1(D_1179,u1_struct_0(B_59))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_59)
      | '#skF_2'('#skF_3',B_59,k9_tmap_1('#skF_3',B_59)) = u1_struct_0(B_59)
      | k9_tmap_1('#skF_3',B_59) != k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52016])).

tff(c_52023,plain,(
    ! [B_1180,D_1181] :
      ( r1_tmap_1(B_1180,k8_tmap_1('#skF_3',B_1180),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_1180),k9_tmap_1('#skF_3',B_1180),B_1180),D_1181)
      | ~ m1_subset_1(D_1181,u1_struct_0(B_1180))
      | ~ m1_subset_1(u1_struct_0(B_1180),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_1180)
      | '#skF_2'('#skF_3',B_1180,k9_tmap_1('#skF_3',B_1180)) = u1_struct_0(B_1180)
      | k9_tmap_1('#skF_3',B_1180) != k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_1180,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_52021])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_52026,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_4')
    | '#skF_2'('#skF_3','#skF_4',k9_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) != k9_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52023,c_48])).

tff(c_52062,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_4')
    | '#skF_2'('#skF_3','#skF_4',k9_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) != k9_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_52026])).

tff(c_52063,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | '#skF_2'('#skF_3','#skF_4',k9_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) != k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52062])).

tff(c_52064,plain,(
    k6_partfun1(u1_struct_0('#skF_3')) != k9_tmap_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52063])).

tff(c_1200,plain,(
    ! [A_290,B_291,C_292] :
      ( m1_subset_1('#skF_2'(A_290,B_291,C_292),k1_zfmisc_1(u1_struct_0(A_290)))
      | k9_tmap_1(A_290,B_291) = C_292
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_290),u1_struct_0(A_290))))
      | ~ v1_funct_2(C_292,u1_struct_0(A_290),u1_struct_0(k8_tmap_1(A_290,B_291)))
      | ~ v1_funct_1(C_292)
      | ~ m1_pre_topc(B_291,A_290)
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290)
      | ~ m1_pre_topc(B_291,A_290)
      | v2_struct_0(B_291)
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_427])).

tff(c_1202,plain,(
    ! [B_291] :
      ( m1_subset_1('#skF_2'('#skF_3',B_291,k6_partfun1(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_291) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_291)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_291,'#skF_3')
      | v2_struct_0(B_291)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_917,c_1200])).

tff(c_1211,plain,(
    ! [B_291] :
      ( m1_subset_1('#skF_2'('#skF_3',B_291,k6_partfun1(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_291) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_291)))
      | ~ m1_pre_topc(B_291,'#skF_3')
      | v2_struct_0(B_291)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_141,c_1202])).

tff(c_1214,plain,(
    ! [B_293] :
      ( m1_subset_1('#skF_2'('#skF_3',B_293,k6_partfun1(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_293) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_293)))
      | ~ m1_pre_topc(B_293,'#skF_3')
      | v2_struct_0(B_293) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1211])).

tff(c_1225,plain,(
    ! [B_79] :
      ( m1_subset_1('#skF_2'('#skF_3',B_79,k6_partfun1(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1214])).

tff(c_1232,plain,(
    ! [B_79] :
      ( m1_subset_1('#skF_2'('#skF_3',B_79,k6_partfun1(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_897,c_1225])).

tff(c_1233,plain,(
    ! [B_79] :
      ( m1_subset_1('#skF_2'('#skF_3',B_79,k6_partfun1(u1_struct_0('#skF_3'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_79) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1232])).

tff(c_13770,plain,(
    ! [B_907,B_908] :
      ( m1_subset_1(u1_struct_0(B_907),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_907) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_907,'#skF_3')
      | v2_struct_0(B_907)
      | k9_tmap_1('#skF_3',B_907) = k7_tmap_1('#skF_3',u1_struct_0(B_908))
      | v2_struct_0(B_908)
      | ~ m1_pre_topc(B_907,'#skF_3')
      | v2_struct_0(B_907)
      | k9_tmap_1('#skF_3',B_908) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_908,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6580,c_1233])).

tff(c_13988,plain,(
    ! [B_907,B_908] :
      ( k9_tmap_1('#skF_3',B_907) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_908,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | m1_subset_1(u1_struct_0(B_907),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_907) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_907,'#skF_3')
      | v2_struct_0(B_907)
      | v2_struct_0(B_908)
      | ~ m1_pre_topc(B_907,'#skF_3')
      | v2_struct_0(B_907)
      | k9_tmap_1('#skF_3',B_908) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_908,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13770,c_77])).

tff(c_14136,plain,(
    ! [B_907,B_908] :
      ( v2_struct_0('#skF_3')
      | m1_subset_1(u1_struct_0(B_907),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_907) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0(B_908)
      | ~ m1_pre_topc(B_907,'#skF_3')
      | v2_struct_0(B_907)
      | k9_tmap_1('#skF_3',B_908) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_908,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_13988])).

tff(c_14137,plain,(
    ! [B_907,B_908] :
      ( m1_subset_1(u1_struct_0(B_907),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_907) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0(B_908)
      | ~ m1_pre_topc(B_907,'#skF_3')
      | v2_struct_0(B_907)
      | k9_tmap_1('#skF_3',B_908) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_908,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_14136])).

tff(c_14145,plain,(
    ! [B_909] :
      ( v2_struct_0(B_909)
      | k9_tmap_1('#skF_3',B_909) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_909,'#skF_3') ) ),
    inference(splitLeft,[status(thm)],[c_14137])).

tff(c_14147,plain,
    ( v2_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_14145])).

tff(c_14150,plain,(
    k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_14147])).

tff(c_293,plain,(
    ! [B_84,A_82,D_176] :
      ( r1_tmap_1(B_84,k6_tmap_1(A_82,u1_struct_0(B_84)),k2_tmap_1(A_82,k6_tmap_1(A_82,u1_struct_0(B_84)),k6_partfun1(u1_struct_0(A_82)),B_84),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(B_84))
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
    inference(superposition,[status(thm),theory(equality)],[c_77,c_275])).

tff(c_14241,plain,(
    ! [B_84,D_176] :
      ( r1_tmap_1(B_84,k6_tmap_1('#skF_3',u1_struct_0(B_84)),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_84)),k9_tmap_1('#skF_3','#skF_4'),B_84),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(B_84))
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
    inference(superposition,[status(thm),theory(equality)],[c_14150,c_293])).

tff(c_14301,plain,(
    ! [B_84,D_176] :
      ( r1_tmap_1(B_84,k6_tmap_1('#skF_3',u1_struct_0(B_84)),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_84)),k9_tmap_1('#skF_3','#skF_4'),B_84),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(B_84))
      | v2_struct_0(B_84)
      | ~ m1_subset_1(u1_struct_0(B_84),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_84,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_58,c_56,c_14241])).

tff(c_15672,plain,(
    ! [B_979,D_980] :
      ( r1_tmap_1(B_979,k6_tmap_1('#skF_3',u1_struct_0(B_979)),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_979)),k9_tmap_1('#skF_3','#skF_4'),B_979),D_980)
      | ~ m1_subset_1(D_980,u1_struct_0(B_979))
      | v2_struct_0(B_979)
      | ~ m1_subset_1(u1_struct_0(B_979),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_979,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_14301])).

tff(c_15676,plain,(
    ! [B_59,D_980] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_59)),k9_tmap_1('#skF_3','#skF_4'),B_59),D_980)
      | ~ m1_subset_1(D_980,u1_struct_0(B_59))
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_15672])).

tff(c_15688,plain,(
    ! [B_59,D_980] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_59)),k9_tmap_1('#skF_3','#skF_4'),B_59),D_980)
      | ~ m1_subset_1(D_980,u1_struct_0(B_59))
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_15676])).

tff(c_15693,plain,(
    ! [B_981,D_982] :
      ( r1_tmap_1(B_981,k8_tmap_1('#skF_3',B_981),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3',u1_struct_0(B_981)),k9_tmap_1('#skF_3','#skF_4'),B_981),D_982)
      | ~ m1_subset_1(D_982,u1_struct_0(B_981))
      | v2_struct_0(B_981)
      | ~ m1_subset_1(u1_struct_0(B_981),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_981,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_15688])).

tff(c_15697,plain,(
    ! [B_59,D_982] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_59),k9_tmap_1('#skF_3','#skF_4'),B_59),D_982)
      | ~ m1_subset_1(D_982,u1_struct_0(B_59))
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_15693])).

tff(c_15702,plain,(
    ! [B_59,D_982] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_59),k9_tmap_1('#skF_3','#skF_4'),B_59),D_982)
      | ~ m1_subset_1(D_982,u1_struct_0(B_59))
      | v2_struct_0(B_59)
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_15697])).

tff(c_15704,plain,(
    ! [B_983,D_984] :
      ( r1_tmap_1(B_983,k8_tmap_1('#skF_3',B_983),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_983),k9_tmap_1('#skF_3','#skF_4'),B_983),D_984)
      | ~ m1_subset_1(D_984,u1_struct_0(B_983))
      | v2_struct_0(B_983)
      | ~ m1_subset_1(u1_struct_0(B_983),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_983,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_15702])).

tff(c_15707,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_15704,c_48])).

tff(c_15710,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_15707])).

tff(c_15711,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_15710])).

tff(c_15714,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_15711])).

tff(c_15718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_15714])).

tff(c_15719,plain,(
    ! [B_907] :
      ( m1_subset_1(u1_struct_0(B_907),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k9_tmap_1('#skF_3',B_907) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_907,'#skF_3')
      | v2_struct_0(B_907) ) ),
    inference(splitRight,[status(thm)],[c_14137])).

tff(c_33941,plain,(
    ! [B_1096] :
      ( k7_tmap_1('#skF_3',u1_struct_0(B_1096)) = k6_partfun1(u1_struct_0('#skF_3'))
      | k7_tmap_1('#skF_3',u1_struct_0(B_1096)) = k9_tmap_1('#skF_3',B_1096)
      | v2_struct_0(B_1096)
      | '#skF_2'('#skF_3',B_1096,k9_tmap_1('#skF_3',B_1096)) = u1_struct_0(B_1096)
      | ~ m1_pre_topc(B_1096,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_33927])).

tff(c_34309,plain,(
    ! [B_1096,D_176] :
      ( r1_tmap_1(B_1096,k6_tmap_1('#skF_3',u1_struct_0(B_1096)),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_1096),k9_tmap_1('#skF_3',B_1096),B_1096),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(B_1096))
      | ~ m1_pre_topc(B_1096,'#skF_3')
      | v2_struct_0(B_1096)
      | ~ m1_subset_1(u1_struct_0(B_1096),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1096,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | k7_tmap_1('#skF_3',u1_struct_0(B_1096)) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0(B_1096)
      | '#skF_2'('#skF_3',B_1096,k9_tmap_1('#skF_3',B_1096)) = u1_struct_0(B_1096)
      | ~ m1_pre_topc(B_1096,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33941,c_281])).

tff(c_34883,plain,(
    ! [B_1096,D_176] :
      ( r1_tmap_1(B_1096,k6_tmap_1('#skF_3',u1_struct_0(B_1096)),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_1096),k9_tmap_1('#skF_3',B_1096),B_1096),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0(B_1096))
      | ~ m1_subset_1(u1_struct_0(B_1096),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | k7_tmap_1('#skF_3',u1_struct_0(B_1096)) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0(B_1096)
      | '#skF_2'('#skF_3',B_1096,k9_tmap_1('#skF_3',B_1096)) = u1_struct_0(B_1096)
      | ~ m1_pre_topc(B_1096,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_58,c_56,c_34309])).

tff(c_73736,plain,(
    ! [B_1275,D_1276] :
      ( r1_tmap_1(B_1275,k6_tmap_1('#skF_3',u1_struct_0(B_1275)),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_1275),k9_tmap_1('#skF_3',B_1275),B_1275),D_1276)
      | ~ m1_subset_1(D_1276,u1_struct_0(B_1275))
      | ~ m1_subset_1(u1_struct_0(B_1275),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k7_tmap_1('#skF_3',u1_struct_0(B_1275)) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0(B_1275)
      | '#skF_2'('#skF_3',B_1275,k9_tmap_1('#skF_3',B_1275)) = u1_struct_0(B_1275)
      | ~ m1_pre_topc(B_1275,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_34883])).

tff(c_73794,plain,(
    ! [B_59,D_1276] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_59),k9_tmap_1('#skF_3',B_59),B_59),D_1276)
      | ~ m1_subset_1(D_1276,u1_struct_0(B_59))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k7_tmap_1('#skF_3',u1_struct_0(B_59)) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0(B_59)
      | '#skF_2'('#skF_3',B_59,k9_tmap_1('#skF_3',B_59)) = u1_struct_0(B_59)
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ m1_pre_topc(B_59,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_73736])).

tff(c_73799,plain,(
    ! [B_59,D_1276] :
      ( r1_tmap_1(B_59,k8_tmap_1('#skF_3',B_59),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_59),k9_tmap_1('#skF_3',B_59),B_59),D_1276)
      | ~ m1_subset_1(D_1276,u1_struct_0(B_59))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k7_tmap_1('#skF_3',u1_struct_0(B_59)) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0(B_59)
      | '#skF_2'('#skF_3',B_59,k9_tmap_1('#skF_3',B_59)) = u1_struct_0(B_59)
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_73794])).

tff(c_73801,plain,(
    ! [B_1277,D_1278] :
      ( r1_tmap_1(B_1277,k8_tmap_1('#skF_3',B_1277),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3',B_1277),k9_tmap_1('#skF_3',B_1277),B_1277),D_1278)
      | ~ m1_subset_1(D_1278,u1_struct_0(B_1277))
      | ~ m1_subset_1(u1_struct_0(B_1277),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | k7_tmap_1('#skF_3',u1_struct_0(B_1277)) = k6_partfun1(u1_struct_0('#skF_3'))
      | v2_struct_0(B_1277)
      | '#skF_2'('#skF_3',B_1277,k9_tmap_1('#skF_3',B_1277)) = u1_struct_0(B_1277)
      | ~ m1_pre_topc(B_1277,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_73799])).

tff(c_73804,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k6_partfun1(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_4')
    | '#skF_2'('#skF_3','#skF_4',k9_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_73801,c_48])).

tff(c_73861,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k6_partfun1(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_4')
    | '#skF_2'('#skF_3','#skF_4',k9_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_73804])).

tff(c_73862,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k6_partfun1(u1_struct_0('#skF_3'))
    | '#skF_2'('#skF_3','#skF_4',k9_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_73861])).

tff(c_73863,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_73862])).

tff(c_73877,plain,
    ( k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_15719,c_73863])).

tff(c_73883,plain,
    ( k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_73877])).

tff(c_73885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_52064,c_73883])).

tff(c_73887,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_73862])).

tff(c_73896,plain,
    ( k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k6_partfun1(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_73887,c_10])).

tff(c_73914,plain,
    ( k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k6_partfun1(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_73896])).

tff(c_73915,plain,(
    k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k6_partfun1(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_73914])).

tff(c_74238,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_73915,c_265])).

tff(c_74501,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_58,c_56,c_73887,c_74238])).

tff(c_74502,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_74501])).

tff(c_74235,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_73915,c_262])).

tff(c_74498,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_58,c_56,c_73887,c_74235])).

tff(c_74499,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_74498])).

tff(c_75042,plain,(
    ! [A_3,B_4] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),A_3,B_4)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | v1_xboole_0(B_4) ) ),
    inference(resolution,[status(thm)],[c_74499,c_6])).

tff(c_75063,plain,(
    ! [A_3,B_4] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),A_3,B_4)
      | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
      | v1_xboole_0(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74502,c_75042])).

tff(c_76708,plain,(
    v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_75063])).

tff(c_76714,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_76708])).

tff(c_76717,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_76714])).

tff(c_76719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_996,c_76717])).

tff(c_76721,plain,(
    ~ v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_75063])).

tff(c_74247,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_73915,c_30])).

tff(c_74510,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_73887,c_74247])).

tff(c_74511,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_74510])).

tff(c_74244,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))))))
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_73915,c_28])).

tff(c_74507,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))))))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_73887,c_74244])).

tff(c_74508,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_74507])).

tff(c_75082,plain,(
    ! [A_3,B_4] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),A_3,B_4)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | v1_xboole_0(u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))))
      | v1_xboole_0(B_4) ) ),
    inference(resolution,[status(thm)],[c_74508,c_6])).

tff(c_75095,plain,(
    ! [A_3,B_4] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),A_3,B_4)
      | v1_xboole_0(u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))))
      | v1_xboole_0(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_74511,c_75082])).

tff(c_79874,plain,(
    v1_xboole_0(u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_75095])).

tff(c_79903,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_79874])).

tff(c_79906,plain,
    ( v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_79903])).

tff(c_79908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_76721,c_79906])).

tff(c_79909,plain,(
    ! [A_3,B_4] :
      ( r1_funct_2(A_3,B_4,u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),A_3,B_4)
      | v1_xboole_0(B_4) ) ),
    inference(splitRight,[status(thm)],[c_75095])).

tff(c_2890,plain,(
    ! [B_232] :
      ( '#skF_2'('#skF_3',B_232,k7_tmap_1('#skF_3',u1_struct_0(B_232))) = u1_struct_0(B_232)
      | k7_tmap_1('#skF_3',u1_struct_0(B_232)) = k9_tmap_1('#skF_3',B_232)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_232,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_2884])).

tff(c_2905,plain,(
    ! [B_232] :
      ( '#skF_2'('#skF_3',B_232,k7_tmap_1('#skF_3',u1_struct_0(B_232))) = u1_struct_0(B_232)
      | k7_tmap_1('#skF_3',u1_struct_0(B_232)) = k9_tmap_1('#skF_3',B_232)
      | v2_struct_0('#skF_3')
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_141,c_2890])).

tff(c_2906,plain,(
    ! [B_232] :
      ( '#skF_2'('#skF_3',B_232,k7_tmap_1('#skF_3',u1_struct_0(B_232))) = u1_struct_0(B_232)
      | k7_tmap_1('#skF_3',u1_struct_0(B_232)) = k9_tmap_1('#skF_3',B_232)
      | k9_tmap_1('#skF_3',B_232) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_232,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2905])).

tff(c_74199,plain,
    ( '#skF_2'('#skF_3','#skF_4',k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0('#skF_4')
    | k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_73915,c_2906])).

tff(c_74461,plain,
    ( '#skF_2'('#skF_3','#skF_4',k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_73915,c_74199])).

tff(c_74462,plain,(
    '#skF_2'('#skF_3','#skF_4',k6_partfun1(u1_struct_0('#skF_3'))) = u1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52064,c_74461])).

tff(c_467,plain,(
    ! [A_216,B_217,C_218] :
      ( ~ r1_funct_2(u1_struct_0(A_216),u1_struct_0(k8_tmap_1(A_216,B_217)),u1_struct_0(A_216),u1_struct_0(k6_tmap_1(A_216,'#skF_2'(A_216,B_217,C_218))),C_218,k7_tmap_1(A_216,'#skF_2'(A_216,B_217,C_218)))
      | k9_tmap_1(A_216,B_217) = C_218
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216),u1_struct_0(k8_tmap_1(A_216,B_217)))))
      | ~ v1_funct_2(C_218,u1_struct_0(A_216),u1_struct_0(k8_tmap_1(A_216,B_217)))
      | ~ v1_funct_1(C_218)
      | ~ m1_pre_topc(B_217,A_216)
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_473,plain,(
    ! [A_75,B_79,C_218] :
      ( ~ r1_funct_2(u1_struct_0(A_75),u1_struct_0(A_75),u1_struct_0(A_75),u1_struct_0(k6_tmap_1(A_75,'#skF_2'(A_75,B_79,C_218))),C_218,k7_tmap_1(A_75,'#skF_2'(A_75,B_79,C_218)))
      | k9_tmap_1(A_75,B_79) = C_218
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75),u1_struct_0(k8_tmap_1(A_75,B_79)))))
      | ~ v1_funct_2(C_218,u1_struct_0(A_75),u1_struct_0(k8_tmap_1(A_75,B_79)))
      | ~ v1_funct_1(C_218)
      | ~ m1_pre_topc(B_79,A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75)
      | ~ m1_pre_topc(B_79,A_75)
      | v2_struct_0(B_79)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_467])).

tff(c_74668,plain,
    ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))),k6_partfun1(u1_struct_0('#skF_3')),k7_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4',k6_partfun1(u1_struct_0('#skF_3')))))
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4')
    | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_74462,c_473])).

tff(c_74875,plain,
    ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4')
    | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_58,c_56,c_52,c_141,c_73915,c_74462,c_74668])).

tff(c_74876,plain,
    ( ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4')))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_52064,c_74875])).

tff(c_84180,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3',u1_struct_0('#skF_4'))),k6_partfun1(u1_struct_0('#skF_3')),k6_partfun1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74502,c_74499,c_74876])).

tff(c_84183,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_79909,c_84180])).

tff(c_84203,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_917,c_84183])).

tff(c_84205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_84203])).

tff(c_84206,plain,
    ( ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | '#skF_2'('#skF_3','#skF_4',k9_tmap_1('#skF_3','#skF_4')) = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_52063])).

tff(c_84965,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_84206])).

tff(c_84968,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_84965])).

tff(c_84972,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_84968])).

tff(c_84974,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_84206])).

tff(c_84207,plain,(
    k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52063])).

tff(c_84983,plain,
    ( k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k6_partfun1(u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_84974,c_10])).

tff(c_85001,plain,
    ( k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_84207,c_84983])).

tff(c_85002,plain,(
    k7_tmap_1('#skF_3',u1_struct_0('#skF_4')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_85001])).

tff(c_85115,plain,(
    ! [D_176] :
      ( r1_tmap_1('#skF_4',k6_tmap_1('#skF_3',u1_struct_0('#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85002,c_281])).

tff(c_85209,plain,(
    ! [D_176] :
      ( r1_tmap_1('#skF_4',k6_tmap_1('#skF_3',u1_struct_0('#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_176)
      | ~ m1_subset_1(D_176,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_58,c_56,c_84974,c_52,c_85115])).

tff(c_85847,plain,(
    ! [D_1353] :
      ( r1_tmap_1('#skF_4',k6_tmap_1('#skF_3',u1_struct_0('#skF_4')),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_1353)
      | ~ m1_subset_1(D_1353,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_85209])).

tff(c_85850,plain,(
    ! [D_1353] :
      ( r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_1353)
      | ~ m1_subset_1(D_1353,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_85847])).

tff(c_85852,plain,(
    ! [D_1353] :
      ( r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_1353)
      | ~ m1_subset_1(D_1353,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_85850])).

tff(c_85854,plain,(
    ! [D_1354] :
      ( r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),D_1354)
      | ~ m1_subset_1(D_1354,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_85852])).

tff(c_85857,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_85854,c_48])).

tff(c_85861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_85857])).

tff(c_85864,plain,(
    ! [B_1355] :
      ( ~ m1_subset_1(u1_struct_0(B_1355),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_1355)
      | k9_tmap_1('#skF_3',B_1355) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_1355,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_863])).

tff(c_85871,plain,(
    ! [B_84] :
      ( v2_struct_0(B_84)
      | k9_tmap_1('#skF_3',B_84) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_85864])).

tff(c_85875,plain,(
    ! [B_1356] :
      ( v2_struct_0(B_1356)
      | k9_tmap_1('#skF_3',B_1356) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_1356,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_85871])).

tff(c_85877,plain,
    ( v2_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_85875])).

tff(c_85880,plain,(
    k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_85877])).

tff(c_85863,plain,(
    ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_863])).

tff(c_85882,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85880,c_85863])).

tff(c_336,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_252,c_331])).

tff(c_85906,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_85880,c_336])).

tff(c_85931,plain,(
    ! [B_59] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_59)))))
      | ~ m1_subset_1(u1_struct_0(B_59),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_59,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_56,c_58,c_58,c_56,c_85906])).

tff(c_86118,plain,(
    ! [B_1370] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_1370)))))
      | ~ m1_subset_1(u1_struct_0(B_1370),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1370,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_85931])).

tff(c_86130,plain,(
    ! [B_79] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_86118])).

tff(c_86143,plain,(
    ! [B_79] :
      ( m1_subset_1(k9_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_86130])).

tff(c_86145,plain,(
    ! [B_1371] :
      ( ~ m1_subset_1(u1_struct_0(B_1371),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1371,'#skF_3')
      | v2_struct_0(B_1371) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_85882,c_86143])).

tff(c_86152,plain,(
    ! [B_84] :
      ( v2_struct_0(B_84)
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_86145])).

tff(c_86156,plain,(
    ! [B_1372] :
      ( v2_struct_0(B_1372)
      | ~ m1_pre_topc(B_1372,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_86152])).

tff(c_86159,plain,(
    v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_86156])).

tff(c_86163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_86159])).

tff(c_86174,plain,(
    ! [B_1374] :
      ( ~ m1_subset_1(u1_struct_0(B_1374),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0(B_1374)
      | k9_tmap_1('#skF_3',B_1374) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_1374,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_86181,plain,(
    ! [B_84] :
      ( v2_struct_0(B_84)
      | k9_tmap_1('#skF_3',B_84) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_86174])).

tff(c_86185,plain,(
    ! [B_1375] :
      ( v2_struct_0(B_1375)
      | k9_tmap_1('#skF_3',B_1375) = k6_partfun1(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_1375,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_86181])).

tff(c_86187,plain,
    ( v2_struct_0('#skF_4')
    | k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_86185])).

tff(c_86190,plain,(
    k6_partfun1(u1_struct_0('#skF_3')) = k9_tmap_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_86187])).

tff(c_86165,plain,(
    ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_86192,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86190,c_86165])).

tff(c_86217,plain,(
    ! [B_170] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_170)))
      | ~ m1_subset_1(u1_struct_0(B_170),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_170,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_170,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86190,c_259])).

tff(c_86242,plain,(
    ! [B_170] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_170)))
      | ~ m1_subset_1(u1_struct_0(B_170),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_170,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_56,c_58,c_58,c_56,c_86217])).

tff(c_86278,plain,(
    ! [B_1381] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_3',B_1381)))
      | ~ m1_subset_1(u1_struct_0(B_1381),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1381,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_86242])).

tff(c_86282,plain,(
    ! [B_79] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_86278])).

tff(c_86284,plain,(
    ! [B_79] :
      ( v1_funct_2(k9_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(u1_struct_0(B_79),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_79,'#skF_3')
      | v2_struct_0(B_79)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_86282])).

tff(c_86286,plain,(
    ! [B_1382] :
      ( ~ m1_subset_1(u1_struct_0(B_1382),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1382,'#skF_3')
      | v2_struct_0(B_1382) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_86192,c_86284])).

tff(c_86293,plain,(
    ! [B_84] :
      ( v2_struct_0(B_84)
      | ~ m1_pre_topc(B_84,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_86286])).

tff(c_86297,plain,(
    ! [B_1383] :
      ( v2_struct_0(B_1383)
      | ~ m1_pre_topc(B_1383,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_86293])).

tff(c_86300,plain,(
    v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_86297])).

tff(c_86304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_86300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 35.36/24.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.36/24.47  
% 35.36/24.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.36/24.47  %$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 35.36/24.47  
% 35.36/24.47  %Foreground sorts:
% 35.36/24.47  
% 35.36/24.47  
% 35.36/24.47  %Background operators:
% 35.36/24.47  
% 35.36/24.47  
% 35.36/24.47  %Foreground operators:
% 35.36/24.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 35.36/24.47  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 35.36/24.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 35.36/24.47  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 35.36/24.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 35.36/24.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 35.36/24.47  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 35.36/24.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 35.36/24.47  tff('#skF_5', type, '#skF_5': $i).
% 35.36/24.47  tff(k9_tmap_1, type, k9_tmap_1: ($i * $i) > $i).
% 35.36/24.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 35.36/24.47  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 35.36/24.47  tff('#skF_3', type, '#skF_3': $i).
% 35.36/24.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 35.36/24.47  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 35.36/24.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 35.36/24.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 35.36/24.47  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 35.36/24.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 35.36/24.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 35.36/24.47  tff('#skF_4', type, '#skF_4': $i).
% 35.36/24.47  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 35.36/24.47  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 35.36/24.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 35.36/24.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 35.36/24.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 35.36/24.47  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 35.36/24.47  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 35.36/24.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 35.36/24.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 35.36/24.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 35.36/24.47  
% 35.70/24.51  tff(f_224, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tmap_1(B, k8_tmap_1(A, B), k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_tmap_1)).
% 35.70/24.51  tff(f_205, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 35.70/24.51  tff(f_153, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 35.70/24.51  tff(f_97, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 35.70/24.51  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 35.70/24.51  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_tmap_1(A, B) = k6_partfun1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 35.70/24.51  tff(f_138, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 35.70/24.51  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))) => ((C = k9_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => r1_funct_2(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, D)), C, k7_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 35.70/24.51  tff(f_198, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_tmap_1)).
% 35.70/24.51  tff(f_59, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 35.70/24.51  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 35.70/24.51  tff(f_176, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => ((u1_struct_0(C) = B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_tmap_1)).
% 35.70/24.51  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 35.70/24.51  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 35.70/24.51  tff(c_56, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 35.70/24.51  tff(c_46, plain, (![B_84, A_82]: (m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_205])).
% 35.70/24.51  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 35.70/24.51  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 35.70/24.51  tff(c_58, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 35.70/24.51  tff(c_34, plain, (![A_58, B_59]: (l1_pre_topc(k8_tmap_1(A_58, B_59)) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_153])).
% 35.70/24.51  tff(c_38, plain, (![A_58, B_59]: (v1_pre_topc(k8_tmap_1(A_58, B_59)) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_153])).
% 35.70/24.51  tff(c_36, plain, (![A_58, B_59]: (v2_pre_topc(k8_tmap_1(A_58, B_59)) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_153])).
% 35.70/24.51  tff(c_226, plain, (![A_155, B_156]: (k6_tmap_1(A_155, u1_struct_0(B_156))=k8_tmap_1(A_155, B_156) | ~m1_subset_1(u1_struct_0(B_156), k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(k8_tmap_1(A_155, B_156)) | ~v2_pre_topc(k8_tmap_1(A_155, B_156)) | ~v1_pre_topc(k8_tmap_1(A_155, B_156)) | ~m1_pre_topc(B_156, A_155) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_97])).
% 35.70/24.51  tff(c_238, plain, (![A_163, B_164]: (k6_tmap_1(A_163, u1_struct_0(B_164))=k8_tmap_1(A_163, B_164) | ~l1_pre_topc(k8_tmap_1(A_163, B_164)) | ~v2_pre_topc(k8_tmap_1(A_163, B_164)) | ~v1_pre_topc(k8_tmap_1(A_163, B_164)) | ~v2_pre_topc(A_163) | v2_struct_0(A_163) | ~m1_pre_topc(B_164, A_163) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_46, c_226])).
% 35.70/24.51  tff(c_243, plain, (![A_165, B_166]: (k6_tmap_1(A_165, u1_struct_0(B_166))=k8_tmap_1(A_165, B_166) | ~l1_pre_topc(k8_tmap_1(A_165, B_166)) | ~v1_pre_topc(k8_tmap_1(A_165, B_166)) | ~m1_pre_topc(B_166, A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_36, c_238])).
% 35.70/24.51  tff(c_248, plain, (![A_167, B_168]: (k6_tmap_1(A_167, u1_struct_0(B_168))=k8_tmap_1(A_167, B_168) | ~l1_pre_topc(k8_tmap_1(A_167, B_168)) | ~m1_pre_topc(B_168, A_167) | ~l1_pre_topc(A_167) | ~v2_pre_topc(A_167) | v2_struct_0(A_167))), inference(resolution, [status(thm)], [c_38, c_243])).
% 35.70/24.51  tff(c_252, plain, (![A_58, B_59]: (k6_tmap_1(A_58, u1_struct_0(B_59))=k8_tmap_1(A_58, B_59) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(resolution, [status(thm)], [c_34, c_248])).
% 35.70/24.51  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 35.70/24.51  tff(c_73, plain, (![A_103, B_104]: (k7_tmap_1(A_103, B_104)=k6_partfun1(u1_struct_0(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_71])).
% 35.70/24.51  tff(c_78, plain, (![A_105, B_106]: (k7_tmap_1(A_105, u1_struct_0(B_106))=k6_partfun1(u1_struct_0(A_105)) | ~v2_pre_topc(A_105) | v2_struct_0(A_105) | ~m1_pre_topc(B_106, A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_46, c_73])).
% 35.70/24.51  tff(c_67, plain, (![A_99, B_100]: (v1_funct_1(k7_tmap_1(A_99, B_100)) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_138])).
% 35.70/24.51  tff(c_71, plain, (![A_82, B_84]: (v1_funct_1(k7_tmap_1(A_82, u1_struct_0(B_84))) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_46, c_67])).
% 35.70/24.51  tff(c_135, plain, (![A_115, B_116]: (v1_funct_1(k6_partfun1(u1_struct_0(A_115))) | ~v2_pre_topc(A_115) | v2_struct_0(A_115) | ~m1_pre_topc(B_116, A_115) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115) | v2_struct_0(A_115) | ~m1_pre_topc(B_116, A_115) | ~l1_pre_topc(A_115))), inference(superposition, [status(thm), theory('equality')], [c_78, c_71])).
% 35.70/24.51  tff(c_137, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_52, c_135])).
% 35.70/24.51  tff(c_140, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_58, c_137])).
% 35.70/24.51  tff(c_141, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_140])).
% 35.70/24.51  tff(c_253, plain, (![A_169, B_170]: (k6_tmap_1(A_169, u1_struct_0(B_170))=k8_tmap_1(A_169, B_170) | ~m1_pre_topc(B_170, A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_34, c_248])).
% 35.70/24.51  tff(c_77, plain, (![A_82, B_84]: (k7_tmap_1(A_82, u1_struct_0(B_84))=k6_partfun1(u1_struct_0(A_82)) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_46, c_73])).
% 35.70/24.51  tff(c_120, plain, (![A_109, B_110]: (v1_funct_2(k7_tmap_1(A_109, B_110), u1_struct_0(A_109), u1_struct_0(k6_tmap_1(A_109, B_110))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_138])).
% 35.70/24.51  tff(c_126, plain, (![A_82, B_84]: (v1_funct_2(k6_partfun1(u1_struct_0(A_82)), u1_struct_0(A_82), u1_struct_0(k6_tmap_1(A_82, u1_struct_0(B_84)))) | ~m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_77, c_120])).
% 35.70/24.51  tff(c_259, plain, (![A_169, B_170]: (v1_funct_2(k6_partfun1(u1_struct_0(A_169)), u1_struct_0(A_169), u1_struct_0(k8_tmap_1(A_169, B_170))) | ~m1_subset_1(u1_struct_0(B_170), k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | ~m1_pre_topc(B_170, A_169) | ~l1_pre_topc(A_169) | ~m1_pre_topc(B_170, A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(superposition, [status(thm), theory('equality')], [c_253, c_126])).
% 35.70/24.51  tff(c_127, plain, (![A_111, B_112]: (m1_subset_1(k7_tmap_1(A_111, B_112), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_111), u1_struct_0(k6_tmap_1(A_111, B_112))))) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_138])).
% 35.70/24.51  tff(c_331, plain, (![A_188, B_189]: (m1_subset_1(k6_partfun1(u1_struct_0(A_188)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188), u1_struct_0(k6_tmap_1(A_188, u1_struct_0(B_189)))))) | ~m1_subset_1(u1_struct_0(B_189), k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188) | ~m1_pre_topc(B_189, A_188) | ~l1_pre_topc(A_188))), inference(superposition, [status(thm), theory('equality')], [c_77, c_127])).
% 35.70/24.51  tff(c_503, plain, (![A_223, B_224]: (m1_subset_1(k6_partfun1(u1_struct_0(A_223)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_223), u1_struct_0(k8_tmap_1(A_223, B_224))))) | ~m1_subset_1(u1_struct_0(B_224), k1_zfmisc_1(u1_struct_0(A_223))) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223) | ~m1_pre_topc(B_224, A_223) | ~l1_pre_topc(A_223) | ~m1_pre_topc(B_224, A_223) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223))), inference(superposition, [status(thm), theory('equality')], [c_252, c_331])).
% 35.70/24.51  tff(c_24, plain, (![B_46, A_34, C_52]: (u1_struct_0(B_46)='#skF_2'(A_34, B_46, C_52) | k9_tmap_1(A_34, B_46)=C_52 | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))))) | ~v1_funct_2(C_52, u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))) | ~v1_funct_1(C_52) | ~m1_pre_topc(B_46, A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_123])).
% 35.70/24.51  tff(c_552, plain, (![A_227, B_228]: ('#skF_2'(A_227, B_228, k6_partfun1(u1_struct_0(A_227)))=u1_struct_0(B_228) | k9_tmap_1(A_227, B_228)=k6_partfun1(u1_struct_0(A_227)) | ~v1_funct_2(k6_partfun1(u1_struct_0(A_227)), u1_struct_0(A_227), u1_struct_0(k8_tmap_1(A_227, B_228))) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_227))) | ~m1_subset_1(u1_struct_0(B_228), k1_zfmisc_1(u1_struct_0(A_227))) | ~m1_pre_topc(B_228, A_227) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(resolution, [status(thm)], [c_503, c_24])).
% 35.70/24.51  tff(c_566, plain, (![A_229, B_230]: ('#skF_2'(A_229, B_230, k6_partfun1(u1_struct_0(A_229)))=u1_struct_0(B_230) | k9_tmap_1(A_229, B_230)=k6_partfun1(u1_struct_0(A_229)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_229))) | ~m1_subset_1(u1_struct_0(B_230), k1_zfmisc_1(u1_struct_0(A_229))) | ~m1_pre_topc(B_230, A_229) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(resolution, [status(thm)], [c_259, c_552])).
% 35.70/24.51  tff(c_574, plain, (![A_231, B_232]: ('#skF_2'(A_231, B_232, k6_partfun1(u1_struct_0(A_231)))=u1_struct_0(B_232) | k9_tmap_1(A_231, B_232)=k6_partfun1(u1_struct_0(A_231)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_231))) | ~v2_pre_topc(A_231) | v2_struct_0(A_231) | ~m1_pre_topc(B_232, A_231) | ~l1_pre_topc(A_231))), inference(resolution, [status(thm)], [c_46, c_566])).
% 35.70/24.51  tff(c_576, plain, (![B_232]: ('#skF_2'('#skF_3', B_232, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_232) | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_232, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_141, c_574])).
% 35.70/24.51  tff(c_581, plain, (![B_232]: ('#skF_2'('#skF_3', B_232, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_232) | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_232, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_576])).
% 35.70/24.51  tff(c_582, plain, (![B_232]: ('#skF_2'('#skF_3', B_232, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_232) | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_581])).
% 35.70/24.51  tff(c_26, plain, (![A_34, B_46, C_52]: (m1_subset_1('#skF_2'(A_34, B_46, C_52), k1_zfmisc_1(u1_struct_0(A_34))) | k9_tmap_1(A_34, B_46)=C_52 | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))))) | ~v1_funct_2(C_52, u1_struct_0(A_34), u1_struct_0(k8_tmap_1(A_34, B_46))) | ~v1_funct_1(C_52) | ~m1_pre_topc(B_46, A_34) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_123])).
% 35.70/24.51  tff(c_646, plain, (![A_243, B_244]: (m1_subset_1('#skF_2'(A_243, B_244, k6_partfun1(u1_struct_0(A_243))), k1_zfmisc_1(u1_struct_0(A_243))) | k9_tmap_1(A_243, B_244)=k6_partfun1(u1_struct_0(A_243)) | ~v1_funct_2(k6_partfun1(u1_struct_0(A_243)), u1_struct_0(A_243), u1_struct_0(k8_tmap_1(A_243, B_244))) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_243))) | ~m1_subset_1(u1_struct_0(B_244), k1_zfmisc_1(u1_struct_0(A_243))) | ~m1_pre_topc(B_244, A_243) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(resolution, [status(thm)], [c_503, c_26])).
% 35.70/24.51  tff(c_682, plain, (![A_248, B_249]: (m1_subset_1('#skF_2'(A_248, B_249, k6_partfun1(u1_struct_0(A_248))), k1_zfmisc_1(u1_struct_0(A_248))) | k9_tmap_1(A_248, B_249)=k6_partfun1(u1_struct_0(A_248)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_248))) | ~m1_subset_1(u1_struct_0(B_249), k1_zfmisc_1(u1_struct_0(A_248))) | ~m1_pre_topc(B_249, A_248) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(resolution, [status(thm)], [c_259, c_646])).
% 35.70/24.51  tff(c_10, plain, (![A_9, B_11]: (k7_tmap_1(A_9, B_11)=k6_partfun1(u1_struct_0(A_9)) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_71])).
% 35.70/24.51  tff(c_763, plain, (![A_257, B_258]: (k7_tmap_1(A_257, '#skF_2'(A_257, B_258, k6_partfun1(u1_struct_0(A_257))))=k6_partfun1(u1_struct_0(A_257)) | k9_tmap_1(A_257, B_258)=k6_partfun1(u1_struct_0(A_257)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_257))) | ~m1_subset_1(u1_struct_0(B_258), k1_zfmisc_1(u1_struct_0(A_257))) | ~m1_pre_topc(B_258, A_257) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(resolution, [status(thm)], [c_682, c_10])).
% 35.70/24.51  tff(c_771, plain, (![A_259, B_260]: (k7_tmap_1(A_259, '#skF_2'(A_259, B_260, k6_partfun1(u1_struct_0(A_259))))=k6_partfun1(u1_struct_0(A_259)) | k9_tmap_1(A_259, B_260)=k6_partfun1(u1_struct_0(A_259)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_259))) | ~v2_pre_topc(A_259) | v2_struct_0(A_259) | ~m1_pre_topc(B_260, A_259) | ~l1_pre_topc(A_259))), inference(resolution, [status(thm)], [c_46, c_763])).
% 35.70/24.51  tff(c_800, plain, (![B_232]: (k7_tmap_1('#skF_3', u1_struct_0(B_232))=k6_partfun1(u1_struct_0('#skF_3')) | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_232, '#skF_3') | ~l1_pre_topc('#skF_3') | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_771])).
% 35.70/24.51  tff(c_807, plain, (![B_232]: (k7_tmap_1('#skF_3', u1_struct_0(B_232))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_141, c_800])).
% 35.70/24.51  tff(c_809, plain, (![B_261]: (k7_tmap_1('#skF_3', u1_struct_0(B_261))=k6_partfun1(u1_struct_0('#skF_3')) | k9_tmap_1('#skF_3', B_261)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_261, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_807])).
% 35.70/24.51  tff(c_44, plain, (![A_75, B_79]: (u1_struct_0(k8_tmap_1(A_75, B_79))=u1_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | v2_struct_0(B_79) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_198])).
% 35.70/24.51  tff(c_30, plain, (![A_56, B_57]: (v1_funct_2(k7_tmap_1(A_56, B_57), u1_struct_0(A_56), u1_struct_0(k6_tmap_1(A_56, B_57))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_138])).
% 35.70/24.51  tff(c_294, plain, (![A_177, B_178]: (v1_funct_2(k7_tmap_1(A_177, u1_struct_0(B_178)), u1_struct_0(A_177), u1_struct_0(k8_tmap_1(A_177, B_178))) | ~m1_subset_1(u1_struct_0(B_178), k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177) | ~m1_pre_topc(B_178, A_177) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(superposition, [status(thm), theory('equality')], [c_253, c_30])).
% 35.70/24.51  tff(c_303, plain, (![A_75, B_79]: (v1_funct_2(k7_tmap_1(A_75, u1_struct_0(B_79)), u1_struct_0(A_75), u1_struct_0(A_75)) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | v2_struct_0(B_79) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_44, c_294])).
% 35.70/24.51  tff(c_827, plain, (![B_261]: (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_261), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_261, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_261, '#skF_3') | v2_struct_0(B_261) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_261)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_261, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_809, c_303])).
% 35.70/24.51  tff(c_868, plain, (![B_261]: (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_261), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_261) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_261)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_261, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_58, c_56, c_58, c_56, c_827])).
% 35.70/24.51  tff(c_869, plain, (![B_261]: (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_261), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_261) | k9_tmap_1('#skF_3', B_261)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_261, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_868])).
% 35.70/24.51  tff(c_897, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_869])).
% 35.70/24.51  tff(c_28, plain, (![A_56, B_57]: (m1_subset_1(k7_tmap_1(A_56, B_57), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_56), u1_struct_0(k6_tmap_1(A_56, B_57))))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_138])).
% 35.70/24.51  tff(c_347, plain, (![A_190, B_191]: (m1_subset_1(k7_tmap_1(A_190, u1_struct_0(B_191)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_190), u1_struct_0(k8_tmap_1(A_190, B_191))))) | ~m1_subset_1(u1_struct_0(B_191), k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190) | ~m1_pre_topc(B_191, A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(superposition, [status(thm), theory('equality')], [c_253, c_28])).
% 35.70/24.51  tff(c_361, plain, (![A_75, B_79]: (m1_subset_1(k7_tmap_1(A_75, u1_struct_0(B_79)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75), u1_struct_0(A_75)))) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | v2_struct_0(B_79) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_44, c_347])).
% 35.70/24.51  tff(c_821, plain, (![B_261]: (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_261), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_261, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_261, '#skF_3') | v2_struct_0(B_261) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_261)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_261, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_809, c_361])).
% 35.70/24.51  tff(c_862, plain, (![B_261]: (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_261), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_261) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_261)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_261, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_58, c_56, c_58, c_56, c_821])).
% 35.70/24.51  tff(c_863, plain, (![B_261]: (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_261), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_261) | k9_tmap_1('#skF_3', B_261)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_261, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_862])).
% 35.70/24.51  tff(c_917, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_863])).
% 35.70/24.51  tff(c_6, plain, (![A_3, F_8, D_6, C_5, B_4]: (r1_funct_2(A_3, B_4, C_5, D_6, F_8, F_8) | ~m1_subset_1(F_8, k1_zfmisc_1(k2_zfmisc_1(C_5, D_6))) | ~v1_funct_2(F_8, C_5, D_6) | ~m1_subset_1(F_8, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(F_8, A_3, B_4) | ~v1_funct_1(F_8) | v1_xboole_0(D_6) | v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 35.70/24.51  tff(c_919, plain, (![A_3, B_4]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), A_3, B_4) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_4))), inference(resolution, [status(thm)], [c_917, c_6])).
% 35.70/24.51  tff(c_922, plain, (![A_3, B_4]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), A_3, B_4) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_897, c_919])).
% 35.70/24.51  tff(c_981, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_922])).
% 35.70/24.51  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.70/24.51  tff(c_984, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_981, c_4])).
% 35.70/24.51  tff(c_987, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_984])).
% 35.70/24.51  tff(c_990, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_987])).
% 35.70/24.51  tff(c_994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_990])).
% 35.70/24.51  tff(c_996, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_922])).
% 35.70/24.51  tff(c_808, plain, (![B_232]: (k7_tmap_1('#skF_3', u1_struct_0(B_232))=k6_partfun1(u1_struct_0('#skF_3')) | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_807])).
% 35.70/24.51  tff(c_324, plain, (![B_185, A_186, C_187]: (u1_struct_0(B_185)='#skF_2'(A_186, B_185, C_187) | k9_tmap_1(A_186, B_185)=C_187 | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_186), u1_struct_0(k8_tmap_1(A_186, B_185))))) | ~v1_funct_2(C_187, u1_struct_0(A_186), u1_struct_0(k8_tmap_1(A_186, B_185))) | ~v1_funct_1(C_187) | ~m1_pre_topc(B_185, A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_123])).
% 35.70/24.51  tff(c_967, plain, (![B_268, A_269, C_270]: (u1_struct_0(B_268)='#skF_2'(A_269, B_268, C_270) | k9_tmap_1(A_269, B_268)=C_270 | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_269), u1_struct_0(A_269)))) | ~v1_funct_2(C_270, u1_struct_0(A_269), u1_struct_0(k8_tmap_1(A_269, B_268))) | ~v1_funct_1(C_270) | ~m1_pre_topc(B_268, A_269) | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269) | ~m1_pre_topc(B_268, A_269) | v2_struct_0(B_268) | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(superposition, [status(thm), theory('equality')], [c_44, c_324])).
% 35.70/24.51  tff(c_6275, plain, (![A_634, B_635, B_636]: ('#skF_2'(A_634, B_635, k7_tmap_1(A_634, u1_struct_0(B_636)))=u1_struct_0(B_635) | k9_tmap_1(A_634, B_635)=k7_tmap_1(A_634, u1_struct_0(B_636)) | ~v1_funct_2(k7_tmap_1(A_634, u1_struct_0(B_636)), u1_struct_0(A_634), u1_struct_0(k8_tmap_1(A_634, B_635))) | ~v1_funct_1(k7_tmap_1(A_634, u1_struct_0(B_636))) | ~m1_pre_topc(B_635, A_634) | v2_struct_0(B_635) | ~m1_subset_1(u1_struct_0(B_636), k1_zfmisc_1(u1_struct_0(A_634))) | ~m1_pre_topc(B_636, A_634) | v2_struct_0(B_636) | ~l1_pre_topc(A_634) | ~v2_pre_topc(A_634) | v2_struct_0(A_634))), inference(resolution, [status(thm)], [c_361, c_967])).
% 35.70/24.51  tff(c_6290, plain, (![B_635, B_232]: ('#skF_2'('#skF_3', B_635, k7_tmap_1('#skF_3', u1_struct_0(B_232)))=u1_struct_0(B_635) | k9_tmap_1('#skF_3', B_635)=k7_tmap_1('#skF_3', u1_struct_0(B_232)) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_635))) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_232))) | ~m1_pre_topc(B_635, '#skF_3') | v2_struct_0(B_635) | ~m1_subset_1(u1_struct_0(B_232), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_232, '#skF_3') | v2_struct_0(B_232) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_6275])).
% 35.70/24.51  tff(c_6317, plain, (![B_635, B_232]: ('#skF_2'('#skF_3', B_635, k7_tmap_1('#skF_3', u1_struct_0(B_232)))=u1_struct_0(B_635) | k9_tmap_1('#skF_3', B_635)=k7_tmap_1('#skF_3', u1_struct_0(B_232)) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_635))) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_232))) | ~m1_pre_topc(B_635, '#skF_3') | v2_struct_0(B_635) | ~m1_subset_1(u1_struct_0(B_232), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_232) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_6290])).
% 35.70/24.51  tff(c_6320, plain, (![B_637, B_638]: ('#skF_2'('#skF_3', B_637, k7_tmap_1('#skF_3', u1_struct_0(B_638)))=u1_struct_0(B_637) | k9_tmap_1('#skF_3', B_637)=k7_tmap_1('#skF_3', u1_struct_0(B_638)) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_637))) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_638))) | ~m1_pre_topc(B_637, '#skF_3') | v2_struct_0(B_637) | ~m1_subset_1(u1_struct_0(B_638), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_638) | k9_tmap_1('#skF_3', B_638)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_638, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_6317])).
% 35.70/24.51  tff(c_6332, plain, (![B_79, B_638]: ('#skF_2'('#skF_3', B_79, k7_tmap_1('#skF_3', u1_struct_0(B_638)))=u1_struct_0(B_79) | k9_tmap_1('#skF_3', B_79)=k7_tmap_1('#skF_3', u1_struct_0(B_638)) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_638))) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~m1_subset_1(u1_struct_0(B_638), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_638) | k9_tmap_1('#skF_3', B_638)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_638, '#skF_3') | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_6320])).
% 35.70/24.51  tff(c_6341, plain, (![B_79, B_638]: ('#skF_2'('#skF_3', B_79, k7_tmap_1('#skF_3', u1_struct_0(B_638)))=u1_struct_0(B_79) | k9_tmap_1('#skF_3', B_79)=k7_tmap_1('#skF_3', u1_struct_0(B_638)) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_638))) | ~m1_subset_1(u1_struct_0(B_638), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_638) | k9_tmap_1('#skF_3', B_638)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_638, '#skF_3') | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_897, c_6332])).
% 35.70/24.51  tff(c_6343, plain, (![B_639, B_640]: ('#skF_2'('#skF_3', B_639, k7_tmap_1('#skF_3', u1_struct_0(B_640)))=u1_struct_0(B_639) | k9_tmap_1('#skF_3', B_639)=k7_tmap_1('#skF_3', u1_struct_0(B_640)) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_640))) | ~m1_subset_1(u1_struct_0(B_640), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_640) | k9_tmap_1('#skF_3', B_640)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_640, '#skF_3') | ~m1_pre_topc(B_639, '#skF_3') | v2_struct_0(B_639))), inference(negUnitSimplification, [status(thm)], [c_60, c_6341])).
% 35.70/24.51  tff(c_6352, plain, (![B_639, B_84]: ('#skF_2'('#skF_3', B_639, k7_tmap_1('#skF_3', u1_struct_0(B_84)))=u1_struct_0(B_639) | k9_tmap_1('#skF_3', B_639)=k7_tmap_1('#skF_3', u1_struct_0(B_84)) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_84))) | v2_struct_0(B_84) | k9_tmap_1('#skF_3', B_84)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_639, '#skF_3') | v2_struct_0(B_639) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_6343])).
% 35.70/24.51  tff(c_6395, plain, (![B_644, B_645]: ('#skF_2'('#skF_3', B_644, k7_tmap_1('#skF_3', u1_struct_0(B_645)))=u1_struct_0(B_644) | k9_tmap_1('#skF_3', B_644)=k7_tmap_1('#skF_3', u1_struct_0(B_645)) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_645))) | v2_struct_0(B_645) | k9_tmap_1('#skF_3', B_645)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_644, '#skF_3') | v2_struct_0(B_644) | ~m1_pre_topc(B_645, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6352])).
% 35.70/24.51  tff(c_6401, plain, (![B_644, B_232]: ('#skF_2'('#skF_3', B_644, k7_tmap_1('#skF_3', u1_struct_0(B_232)))=u1_struct_0(B_644) | k9_tmap_1('#skF_3', B_644)=k7_tmap_1('#skF_3', u1_struct_0(B_232)) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | v2_struct_0(B_232) | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_644, '#skF_3') | v2_struct_0(B_644) | ~m1_pre_topc(B_232, '#skF_3') | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_6395])).
% 35.70/24.51  tff(c_6424, plain, (![B_646, B_647]: ('#skF_2'('#skF_3', B_646, k7_tmap_1('#skF_3', u1_struct_0(B_647)))=u1_struct_0(B_646) | k9_tmap_1('#skF_3', B_646)=k7_tmap_1('#skF_3', u1_struct_0(B_647)) | v2_struct_0(B_647) | ~m1_pre_topc(B_646, '#skF_3') | v2_struct_0(B_646) | k9_tmap_1('#skF_3', B_647)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_647, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_6401])).
% 35.70/24.51  tff(c_6532, plain, (![B_646, B_84]: ('#skF_2'('#skF_3', B_646, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_646) | k9_tmap_1('#skF_3', B_646)=k7_tmap_1('#skF_3', u1_struct_0(B_84)) | v2_struct_0(B_84) | ~m1_pre_topc(B_646, '#skF_3') | v2_struct_0(B_646) | k9_tmap_1('#skF_3', B_84)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_84, '#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_6424])).
% 35.70/24.51  tff(c_6577, plain, (![B_646, B_84]: ('#skF_2'('#skF_3', B_646, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_646) | k9_tmap_1('#skF_3', B_646)=k7_tmap_1('#skF_3', u1_struct_0(B_84)) | v2_struct_0(B_84) | ~m1_pre_topc(B_646, '#skF_3') | v2_struct_0(B_646) | k9_tmap_1('#skF_3', B_84)=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_6532])).
% 35.70/24.51  tff(c_6580, plain, (![B_648, B_649]: ('#skF_2'('#skF_3', B_648, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_648) | k9_tmap_1('#skF_3', B_648)=k7_tmap_1('#skF_3', u1_struct_0(B_649)) | v2_struct_0(B_649) | ~m1_pre_topc(B_648, '#skF_3') | v2_struct_0(B_648) | k9_tmap_1('#skF_3', B_649)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_649, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_6577])).
% 35.70/24.51  tff(c_265, plain, (![A_169, B_170]: (v1_funct_2(k7_tmap_1(A_169, u1_struct_0(B_170)), u1_struct_0(A_169), u1_struct_0(k8_tmap_1(A_169, B_170))) | ~m1_subset_1(u1_struct_0(B_170), k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | ~m1_pre_topc(B_170, A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(superposition, [status(thm), theory('equality')], [c_253, c_30])).
% 35.70/24.51  tff(c_2784, plain, (![A_439, B_440]: ('#skF_2'(A_439, B_440, k7_tmap_1(A_439, u1_struct_0(B_440)))=u1_struct_0(B_440) | k7_tmap_1(A_439, u1_struct_0(B_440))=k9_tmap_1(A_439, B_440) | ~v1_funct_2(k7_tmap_1(A_439, u1_struct_0(B_440)), u1_struct_0(A_439), u1_struct_0(k8_tmap_1(A_439, B_440))) | ~v1_funct_1(k7_tmap_1(A_439, u1_struct_0(B_440))) | ~m1_subset_1(u1_struct_0(B_440), k1_zfmisc_1(u1_struct_0(A_439))) | ~m1_pre_topc(B_440, A_439) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | v2_struct_0(A_439))), inference(resolution, [status(thm)], [c_347, c_24])).
% 35.70/24.51  tff(c_2813, plain, (![A_441, B_442]: ('#skF_2'(A_441, B_442, k7_tmap_1(A_441, u1_struct_0(B_442)))=u1_struct_0(B_442) | k7_tmap_1(A_441, u1_struct_0(B_442))=k9_tmap_1(A_441, B_442) | ~v1_funct_1(k7_tmap_1(A_441, u1_struct_0(B_442))) | ~m1_subset_1(u1_struct_0(B_442), k1_zfmisc_1(u1_struct_0(A_441))) | ~m1_pre_topc(B_442, A_441) | ~l1_pre_topc(A_441) | ~v2_pre_topc(A_441) | v2_struct_0(A_441))), inference(resolution, [status(thm)], [c_265, c_2784])).
% 35.70/24.51  tff(c_2884, plain, (![A_445, B_446]: ('#skF_2'(A_445, B_446, k7_tmap_1(A_445, u1_struct_0(B_446)))=u1_struct_0(B_446) | k7_tmap_1(A_445, u1_struct_0(B_446))=k9_tmap_1(A_445, B_446) | ~v1_funct_1(k7_tmap_1(A_445, u1_struct_0(B_446))) | ~v2_pre_topc(A_445) | v2_struct_0(A_445) | ~m1_pre_topc(B_446, A_445) | ~l1_pre_topc(A_445))), inference(resolution, [status(thm)], [c_46, c_2813])).
% 35.70/24.51  tff(c_2912, plain, (![A_82, B_84]: ('#skF_2'(A_82, B_84, k7_tmap_1(A_82, u1_struct_0(B_84)))=u1_struct_0(B_84) | k7_tmap_1(A_82, u1_struct_0(B_84))=k9_tmap_1(A_82, B_84) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(resolution, [status(thm)], [c_71, c_2884])).
% 35.70/24.51  tff(c_6779, plain, (![B_649, B_648]: ('#skF_2'('#skF_3', B_649, k9_tmap_1('#skF_3', B_648))=u1_struct_0(B_649) | k7_tmap_1('#skF_3', u1_struct_0(B_649))=k9_tmap_1('#skF_3', B_649) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_649, '#skF_3') | ~l1_pre_topc('#skF_3') | '#skF_2'('#skF_3', B_648, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_648) | v2_struct_0(B_649) | ~m1_pre_topc(B_648, '#skF_3') | v2_struct_0(B_648) | k9_tmap_1('#skF_3', B_649)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_649, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6580, c_2912])).
% 35.70/24.51  tff(c_6967, plain, (![B_649, B_648]: ('#skF_2'('#skF_3', B_649, k9_tmap_1('#skF_3', B_648))=u1_struct_0(B_649) | k7_tmap_1('#skF_3', u1_struct_0(B_649))=k9_tmap_1('#skF_3', B_649) | v2_struct_0('#skF_3') | '#skF_2'('#skF_3', B_648, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_648) | v2_struct_0(B_649) | ~m1_pre_topc(B_648, '#skF_3') | v2_struct_0(B_648) | k9_tmap_1('#skF_3', B_649)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_649, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_6779])).
% 35.70/24.51  tff(c_10271, plain, (![B_805, B_806]: ('#skF_2'('#skF_3', B_805, k9_tmap_1('#skF_3', B_806))=u1_struct_0(B_805) | k7_tmap_1('#skF_3', u1_struct_0(B_805))=k9_tmap_1('#skF_3', B_805) | '#skF_2'('#skF_3', B_806, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_806) | v2_struct_0(B_805) | ~m1_pre_topc(B_806, '#skF_3') | v2_struct_0(B_806) | k9_tmap_1('#skF_3', B_805)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_805, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_6967])).
% 35.70/24.51  tff(c_10426, plain, (![B_805, B_806]: (k9_tmap_1('#skF_3', B_805)=k6_partfun1(u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_805, '#skF_3') | ~l1_pre_topc('#skF_3') | '#skF_2'('#skF_3', B_805, k9_tmap_1('#skF_3', B_806))=u1_struct_0(B_805) | '#skF_2'('#skF_3', B_806, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_806) | v2_struct_0(B_805) | ~m1_pre_topc(B_806, '#skF_3') | v2_struct_0(B_806) | k9_tmap_1('#skF_3', B_805)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_805, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10271, c_77])).
% 35.70/24.51  tff(c_10672, plain, (![B_805, B_806]: (v2_struct_0('#skF_3') | '#skF_2'('#skF_3', B_805, k9_tmap_1('#skF_3', B_806))=u1_struct_0(B_805) | '#skF_2'('#skF_3', B_806, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_806) | v2_struct_0(B_805) | ~m1_pre_topc(B_806, '#skF_3') | v2_struct_0(B_806) | k9_tmap_1('#skF_3', B_805)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_805, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_10426])).
% 35.70/24.51  tff(c_10741, plain, (![B_807, B_808]: ('#skF_2'('#skF_3', B_807, k9_tmap_1('#skF_3', B_808))=u1_struct_0(B_807) | '#skF_2'('#skF_3', B_808, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_808) | v2_struct_0(B_807) | ~m1_pre_topc(B_808, '#skF_3') | v2_struct_0(B_808) | k9_tmap_1('#skF_3', B_807)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_807, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_10672])).
% 35.70/24.51  tff(c_2972, plain, (![A_450, B_451]: ('#skF_2'(A_450, B_451, k7_tmap_1(A_450, u1_struct_0(B_451)))=u1_struct_0(B_451) | k7_tmap_1(A_450, u1_struct_0(B_451))=k9_tmap_1(A_450, B_451) | ~v2_pre_topc(A_450) | v2_struct_0(A_450) | ~m1_pre_topc(B_451, A_450) | ~l1_pre_topc(A_450))), inference(resolution, [status(thm)], [c_71, c_2884])).
% 35.70/24.51  tff(c_3012, plain, (![A_82, B_84]: ('#skF_2'(A_82, B_84, k6_partfun1(u1_struct_0(A_82)))=u1_struct_0(B_84) | k7_tmap_1(A_82, u1_struct_0(B_84))=k9_tmap_1(A_82, B_84) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_77, c_2972])).
% 35.70/24.51  tff(c_10925, plain, (![B_84, B_807, B_808]: ('#skF_2'('#skF_3', B_84, k9_tmap_1('#skF_3', B_807))=u1_struct_0(B_84) | k7_tmap_1('#skF_3', u1_struct_0(B_84))=k9_tmap_1('#skF_3', B_84) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3') | '#skF_2'('#skF_3', B_807, k9_tmap_1('#skF_3', B_808))=u1_struct_0(B_807) | '#skF_2'('#skF_3', B_808, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_808) | v2_struct_0(B_807) | ~m1_pre_topc(B_808, '#skF_3') | v2_struct_0(B_808) | ~m1_pre_topc(B_807, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10741, c_3012])).
% 35.70/24.51  tff(c_11121, plain, (![B_84, B_807, B_808]: ('#skF_2'('#skF_3', B_84, k9_tmap_1('#skF_3', B_807))=u1_struct_0(B_84) | k7_tmap_1('#skF_3', u1_struct_0(B_84))=k9_tmap_1('#skF_3', B_84) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3') | '#skF_2'('#skF_3', B_807, k9_tmap_1('#skF_3', B_808))=u1_struct_0(B_807) | '#skF_2'('#skF_3', B_808, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_808) | v2_struct_0(B_807) | ~m1_pre_topc(B_808, '#skF_3') | v2_struct_0(B_808) | ~m1_pre_topc(B_807, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_56, c_58, c_10925])).
% 35.70/24.51  tff(c_11122, plain, (![B_84, B_807, B_808]: ('#skF_2'('#skF_3', B_84, k9_tmap_1('#skF_3', B_807))=u1_struct_0(B_84) | k7_tmap_1('#skF_3', u1_struct_0(B_84))=k9_tmap_1('#skF_3', B_84) | ~m1_pre_topc(B_84, '#skF_3') | '#skF_2'('#skF_3', B_807, k9_tmap_1('#skF_3', B_808))=u1_struct_0(B_807) | '#skF_2'('#skF_3', B_808, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_808) | v2_struct_0(B_807) | ~m1_pre_topc(B_808, '#skF_3') | v2_struct_0(B_808) | ~m1_pre_topc(B_807, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_11121])).
% 35.70/24.51  tff(c_33324, plain, (![B_1090]: (k7_tmap_1('#skF_3', u1_struct_0(B_1090))=k9_tmap_1('#skF_3', B_1090) | '#skF_2'('#skF_3', B_1090, k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0(B_1090) | v2_struct_0(B_1090) | ~m1_pre_topc(B_1090, '#skF_3') | '#skF_2'('#skF_3', B_1090, k9_tmap_1('#skF_3', B_1090))=u1_struct_0(B_1090))), inference(factorization, [status(thm), theory('equality')], [c_11122])).
% 35.70/24.51  tff(c_262, plain, (![A_169, B_170]: (m1_subset_1(k7_tmap_1(A_169, u1_struct_0(B_170)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_169), u1_struct_0(k8_tmap_1(A_169, B_170))))) | ~m1_subset_1(u1_struct_0(B_170), k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169) | ~m1_pre_topc(B_170, A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(superposition, [status(thm), theory('equality')], [c_253, c_28])).
% 35.70/24.51  tff(c_427, plain, (![A_201, B_202, C_203]: (m1_subset_1('#skF_2'(A_201, B_202, C_203), k1_zfmisc_1(u1_struct_0(A_201))) | k9_tmap_1(A_201, B_202)=C_203 | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_201), u1_struct_0(k8_tmap_1(A_201, B_202))))) | ~v1_funct_2(C_203, u1_struct_0(A_201), u1_struct_0(k8_tmap_1(A_201, B_202))) | ~v1_funct_1(C_203) | ~m1_pre_topc(B_202, A_201) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_123])).
% 35.70/24.51  tff(c_4089, plain, (![A_523, B_524]: (m1_subset_1('#skF_2'(A_523, B_524, k7_tmap_1(A_523, u1_struct_0(B_524))), k1_zfmisc_1(u1_struct_0(A_523))) | k7_tmap_1(A_523, u1_struct_0(B_524))=k9_tmap_1(A_523, B_524) | ~v1_funct_2(k7_tmap_1(A_523, u1_struct_0(B_524)), u1_struct_0(A_523), u1_struct_0(k8_tmap_1(A_523, B_524))) | ~v1_funct_1(k7_tmap_1(A_523, u1_struct_0(B_524))) | ~m1_subset_1(u1_struct_0(B_524), k1_zfmisc_1(u1_struct_0(A_523))) | ~m1_pre_topc(B_524, A_523) | ~l1_pre_topc(A_523) | ~v2_pre_topc(A_523) | v2_struct_0(A_523))), inference(resolution, [status(thm)], [c_262, c_427])).
% 35.70/24.51  tff(c_4121, plain, (![A_525, B_526]: (m1_subset_1('#skF_2'(A_525, B_526, k7_tmap_1(A_525, u1_struct_0(B_526))), k1_zfmisc_1(u1_struct_0(A_525))) | k7_tmap_1(A_525, u1_struct_0(B_526))=k9_tmap_1(A_525, B_526) | ~v1_funct_1(k7_tmap_1(A_525, u1_struct_0(B_526))) | ~m1_subset_1(u1_struct_0(B_526), k1_zfmisc_1(u1_struct_0(A_525))) | ~m1_pre_topc(B_526, A_525) | ~l1_pre_topc(A_525) | ~v2_pre_topc(A_525) | v2_struct_0(A_525))), inference(resolution, [status(thm)], [c_265, c_4089])).
% 35.70/24.51  tff(c_4206, plain, (![A_533, B_534]: (k7_tmap_1(A_533, '#skF_2'(A_533, B_534, k7_tmap_1(A_533, u1_struct_0(B_534))))=k6_partfun1(u1_struct_0(A_533)) | k7_tmap_1(A_533, u1_struct_0(B_534))=k9_tmap_1(A_533, B_534) | ~v1_funct_1(k7_tmap_1(A_533, u1_struct_0(B_534))) | ~m1_subset_1(u1_struct_0(B_534), k1_zfmisc_1(u1_struct_0(A_533))) | ~m1_pre_topc(B_534, A_533) | ~l1_pre_topc(A_533) | ~v2_pre_topc(A_533) | v2_struct_0(A_533))), inference(resolution, [status(thm)], [c_4121, c_10])).
% 35.70/24.51  tff(c_4226, plain, (![A_535, B_536]: (k7_tmap_1(A_535, '#skF_2'(A_535, B_536, k7_tmap_1(A_535, u1_struct_0(B_536))))=k6_partfun1(u1_struct_0(A_535)) | k7_tmap_1(A_535, u1_struct_0(B_536))=k9_tmap_1(A_535, B_536) | ~v1_funct_1(k7_tmap_1(A_535, u1_struct_0(B_536))) | ~v2_pre_topc(A_535) | v2_struct_0(A_535) | ~m1_pre_topc(B_536, A_535) | ~l1_pre_topc(A_535))), inference(resolution, [status(thm)], [c_46, c_4206])).
% 35.70/24.51  tff(c_4285, plain, (![A_82, B_84]: (k7_tmap_1(A_82, '#skF_2'(A_82, B_84, k6_partfun1(u1_struct_0(A_82))))=k6_partfun1(u1_struct_0(A_82)) | k7_tmap_1(A_82, u1_struct_0(B_84))=k9_tmap_1(A_82, B_84) | ~v1_funct_1(k7_tmap_1(A_82, u1_struct_0(B_84))) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_77, c_4226])).
% 35.70/24.51  tff(c_33378, plain, (![B_1090]: (k7_tmap_1('#skF_3', u1_struct_0(B_1090))=k6_partfun1(u1_struct_0('#skF_3')) | k7_tmap_1('#skF_3', u1_struct_0(B_1090))=k9_tmap_1('#skF_3', B_1090) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_1090))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_1090, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_1090, '#skF_3') | ~l1_pre_topc('#skF_3') | k7_tmap_1('#skF_3', u1_struct_0(B_1090))=k9_tmap_1('#skF_3', B_1090) | v2_struct_0(B_1090) | ~m1_pre_topc(B_1090, '#skF_3') | '#skF_2'('#skF_3', B_1090, k9_tmap_1('#skF_3', B_1090))=u1_struct_0(B_1090))), inference(superposition, [status(thm), theory('equality')], [c_33324, c_4285])).
% 35.70/24.51  tff(c_33718, plain, (![B_1090]: (k7_tmap_1('#skF_3', u1_struct_0(B_1090))=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_1090))) | v2_struct_0('#skF_3') | k7_tmap_1('#skF_3', u1_struct_0(B_1090))=k9_tmap_1('#skF_3', B_1090) | v2_struct_0(B_1090) | ~m1_pre_topc(B_1090, '#skF_3') | '#skF_2'('#skF_3', B_1090, k9_tmap_1('#skF_3', B_1090))=u1_struct_0(B_1090))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_56, c_58, c_33378])).
% 35.70/24.51  tff(c_33834, plain, (![B_1095]: (k7_tmap_1('#skF_3', u1_struct_0(B_1095))=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_1(k7_tmap_1('#skF_3', u1_struct_0(B_1095))) | k7_tmap_1('#skF_3', u1_struct_0(B_1095))=k9_tmap_1('#skF_3', B_1095) | v2_struct_0(B_1095) | ~m1_pre_topc(B_1095, '#skF_3') | '#skF_2'('#skF_3', B_1095, k9_tmap_1('#skF_3', B_1095))=u1_struct_0(B_1095))), inference(negUnitSimplification, [status(thm)], [c_60, c_33718])).
% 35.70/24.51  tff(c_33897, plain, (![B_84]: (k7_tmap_1('#skF_3', u1_struct_0(B_84))=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | k7_tmap_1('#skF_3', u1_struct_0(B_84))=k9_tmap_1('#skF_3', B_84) | v2_struct_0(B_84) | ~m1_pre_topc(B_84, '#skF_3') | '#skF_2'('#skF_3', B_84, k9_tmap_1('#skF_3', B_84))=u1_struct_0(B_84) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_33834])).
% 35.70/24.51  tff(c_33927, plain, (![B_84]: (k7_tmap_1('#skF_3', u1_struct_0(B_84))=k6_partfun1(u1_struct_0('#skF_3')) | k7_tmap_1('#skF_3', u1_struct_0(B_84))=k9_tmap_1('#skF_3', B_84) | v2_struct_0(B_84) | '#skF_2'('#skF_3', B_84, k9_tmap_1('#skF_3', B_84))=u1_struct_0(B_84) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_141, c_33897])).
% 35.70/24.51  tff(c_33928, plain, (![B_84]: (k7_tmap_1('#skF_3', u1_struct_0(B_84))=k6_partfun1(u1_struct_0('#skF_3')) | k7_tmap_1('#skF_3', u1_struct_0(B_84))=k9_tmap_1('#skF_3', B_84) | v2_struct_0(B_84) | '#skF_2'('#skF_3', B_84, k9_tmap_1('#skF_3', B_84))=u1_struct_0(B_84) | ~m1_pre_topc(B_84, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_33927])).
% 35.70/24.51  tff(c_35644, plain, (![B_1098]: (v2_struct_0(B_1098) | '#skF_2'('#skF_3', B_1098, k9_tmap_1('#skF_3', B_1098))=u1_struct_0(B_1098) | ~m1_pre_topc(B_1098, '#skF_3') | k7_tmap_1('#skF_3', u1_struct_0(B_1098))=k9_tmap_1('#skF_3', B_1098) | k9_tmap_1('#skF_3', B_1098)!=k6_partfun1(u1_struct_0('#skF_3')))), inference(factorization, [status(thm), theory('equality')], [c_33928])).
% 35.70/24.51  tff(c_275, plain, (![C_174, A_175, D_176]: (r1_tmap_1(C_174, k6_tmap_1(A_175, u1_struct_0(C_174)), k2_tmap_1(A_175, k6_tmap_1(A_175, u1_struct_0(C_174)), k7_tmap_1(A_175, u1_struct_0(C_174)), C_174), D_176) | ~m1_subset_1(D_176, u1_struct_0(C_174)) | ~m1_pre_topc(C_174, A_175) | v2_struct_0(C_174) | ~m1_subset_1(u1_struct_0(C_174), k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_176])).
% 35.70/24.51  tff(c_281, plain, (![B_59, A_58, D_176]: (r1_tmap_1(B_59, k6_tmap_1(A_58, u1_struct_0(B_59)), k2_tmap_1(A_58, k8_tmap_1(A_58, B_59), k7_tmap_1(A_58, u1_struct_0(B_59)), B_59), D_176) | ~m1_subset_1(D_176, u1_struct_0(B_59)) | ~m1_pre_topc(B_59, A_58) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_252, c_275])).
% 35.70/24.51  tff(c_35903, plain, (![B_1098, D_176]: (r1_tmap_1(B_1098, k6_tmap_1('#skF_3', u1_struct_0(B_1098)), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_1098), k9_tmap_1('#skF_3', B_1098), B_1098), D_176) | ~m1_subset_1(D_176, u1_struct_0(B_1098)) | ~m1_pre_topc(B_1098, '#skF_3') | v2_struct_0(B_1098) | ~m1_subset_1(u1_struct_0(B_1098), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_1098, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v2_struct_0(B_1098) | '#skF_2'('#skF_3', B_1098, k9_tmap_1('#skF_3', B_1098))=u1_struct_0(B_1098) | ~m1_pre_topc(B_1098, '#skF_3') | k9_tmap_1('#skF_3', B_1098)!=k6_partfun1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_35644, c_281])).
% 35.70/24.51  tff(c_36251, plain, (![B_1098, D_176]: (r1_tmap_1(B_1098, k6_tmap_1('#skF_3', u1_struct_0(B_1098)), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_1098), k9_tmap_1('#skF_3', B_1098), B_1098), D_176) | ~m1_subset_1(D_176, u1_struct_0(B_1098)) | ~m1_subset_1(u1_struct_0(B_1098), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | v2_struct_0(B_1098) | '#skF_2'('#skF_3', B_1098, k9_tmap_1('#skF_3', B_1098))=u1_struct_0(B_1098) | ~m1_pre_topc(B_1098, '#skF_3') | k9_tmap_1('#skF_3', B_1098)!=k6_partfun1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_58, c_56, c_35903])).
% 35.70/24.51  tff(c_51979, plain, (![B_1178, D_1179]: (r1_tmap_1(B_1178, k6_tmap_1('#skF_3', u1_struct_0(B_1178)), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_1178), k9_tmap_1('#skF_3', B_1178), B_1178), D_1179) | ~m1_subset_1(D_1179, u1_struct_0(B_1178)) | ~m1_subset_1(u1_struct_0(B_1178), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_1178) | '#skF_2'('#skF_3', B_1178, k9_tmap_1('#skF_3', B_1178))=u1_struct_0(B_1178) | ~m1_pre_topc(B_1178, '#skF_3') | k9_tmap_1('#skF_3', B_1178)!=k6_partfun1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_60, c_36251])).
% 35.70/24.51  tff(c_52016, plain, (![B_59, D_1179]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_59), k9_tmap_1('#skF_3', B_59), B_59), D_1179) | ~m1_subset_1(D_1179, u1_struct_0(B_59)) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_59) | '#skF_2'('#skF_3', B_59, k9_tmap_1('#skF_3', B_59))=u1_struct_0(B_59) | ~m1_pre_topc(B_59, '#skF_3') | k9_tmap_1('#skF_3', B_59)!=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_252, c_51979])).
% 35.70/24.51  tff(c_52021, plain, (![B_59, D_1179]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_59), k9_tmap_1('#skF_3', B_59), B_59), D_1179) | ~m1_subset_1(D_1179, u1_struct_0(B_59)) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_59) | '#skF_2'('#skF_3', B_59, k9_tmap_1('#skF_3', B_59))=u1_struct_0(B_59) | k9_tmap_1('#skF_3', B_59)!=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52016])).
% 35.70/24.51  tff(c_52023, plain, (![B_1180, D_1181]: (r1_tmap_1(B_1180, k8_tmap_1('#skF_3', B_1180), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_1180), k9_tmap_1('#skF_3', B_1180), B_1180), D_1181) | ~m1_subset_1(D_1181, u1_struct_0(B_1180)) | ~m1_subset_1(u1_struct_0(B_1180), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_1180) | '#skF_2'('#skF_3', B_1180, k9_tmap_1('#skF_3', B_1180))=u1_struct_0(B_1180) | k9_tmap_1('#skF_3', B_1180)!=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_1180, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_52021])).
% 35.70/24.51  tff(c_48, plain, (~r1_tmap_1('#skF_4', k8_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', '#skF_4'), k9_tmap_1('#skF_3', '#skF_4'), '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 35.70/24.51  tff(c_52026, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_4') | '#skF_2'('#skF_3', '#skF_4', k9_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))!=k9_tmap_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52023, c_48])).
% 35.70/24.51  tff(c_52062, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_4') | '#skF_2'('#skF_3', '#skF_4', k9_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))!=k9_tmap_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_52026])).
% 35.70/24.51  tff(c_52063, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | '#skF_2'('#skF_3', '#skF_4', k9_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))!=k9_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_52062])).
% 35.70/24.51  tff(c_52064, plain, (k6_partfun1(u1_struct_0('#skF_3'))!=k9_tmap_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_52063])).
% 35.70/24.51  tff(c_1200, plain, (![A_290, B_291, C_292]: (m1_subset_1('#skF_2'(A_290, B_291, C_292), k1_zfmisc_1(u1_struct_0(A_290))) | k9_tmap_1(A_290, B_291)=C_292 | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_290), u1_struct_0(A_290)))) | ~v1_funct_2(C_292, u1_struct_0(A_290), u1_struct_0(k8_tmap_1(A_290, B_291))) | ~v1_funct_1(C_292) | ~m1_pre_topc(B_291, A_290) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290) | ~m1_pre_topc(B_291, A_290) | v2_struct_0(B_291) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290))), inference(superposition, [status(thm), theory('equality')], [c_44, c_427])).
% 35.70/24.51  tff(c_1202, plain, (![B_291]: (m1_subset_1('#skF_2'('#skF_3', B_291, k6_partfun1(u1_struct_0('#skF_3'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_291)=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_291))) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_291, '#skF_3') | v2_struct_0(B_291) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_917, c_1200])).
% 35.70/24.51  tff(c_1211, plain, (![B_291]: (m1_subset_1('#skF_2'('#skF_3', B_291, k6_partfun1(u1_struct_0('#skF_3'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_291)=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_291))) | ~m1_pre_topc(B_291, '#skF_3') | v2_struct_0(B_291) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_141, c_1202])).
% 35.70/24.51  tff(c_1214, plain, (![B_293]: (m1_subset_1('#skF_2'('#skF_3', B_293, k6_partfun1(u1_struct_0('#skF_3'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_293)=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_293))) | ~m1_pre_topc(B_293, '#skF_3') | v2_struct_0(B_293))), inference(negUnitSimplification, [status(thm)], [c_60, c_1211])).
% 35.70/24.51  tff(c_1225, plain, (![B_79]: (m1_subset_1('#skF_2'('#skF_3', B_79, k6_partfun1(u1_struct_0('#skF_3'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1214])).
% 35.70/24.51  tff(c_1232, plain, (![B_79]: (m1_subset_1('#skF_2'('#skF_3', B_79, k6_partfun1(u1_struct_0('#skF_3'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_897, c_1225])).
% 35.70/24.51  tff(c_1233, plain, (![B_79]: (m1_subset_1('#skF_2'('#skF_3', B_79, k6_partfun1(u1_struct_0('#skF_3'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_79)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79))), inference(negUnitSimplification, [status(thm)], [c_60, c_1232])).
% 35.70/24.51  tff(c_13770, plain, (![B_907, B_908]: (m1_subset_1(u1_struct_0(B_907), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_907)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_907, '#skF_3') | v2_struct_0(B_907) | k9_tmap_1('#skF_3', B_907)=k7_tmap_1('#skF_3', u1_struct_0(B_908)) | v2_struct_0(B_908) | ~m1_pre_topc(B_907, '#skF_3') | v2_struct_0(B_907) | k9_tmap_1('#skF_3', B_908)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_908, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6580, c_1233])).
% 35.70/24.51  tff(c_13988, plain, (![B_907, B_908]: (k9_tmap_1('#skF_3', B_907)=k6_partfun1(u1_struct_0('#skF_3')) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_908, '#skF_3') | ~l1_pre_topc('#skF_3') | m1_subset_1(u1_struct_0(B_907), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_907)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_907, '#skF_3') | v2_struct_0(B_907) | v2_struct_0(B_908) | ~m1_pre_topc(B_907, '#skF_3') | v2_struct_0(B_907) | k9_tmap_1('#skF_3', B_908)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_908, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_13770, c_77])).
% 35.70/24.51  tff(c_14136, plain, (![B_907, B_908]: (v2_struct_0('#skF_3') | m1_subset_1(u1_struct_0(B_907), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_907)=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0(B_908) | ~m1_pre_topc(B_907, '#skF_3') | v2_struct_0(B_907) | k9_tmap_1('#skF_3', B_908)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_908, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_13988])).
% 35.70/24.51  tff(c_14137, plain, (![B_907, B_908]: (m1_subset_1(u1_struct_0(B_907), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_907)=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0(B_908) | ~m1_pre_topc(B_907, '#skF_3') | v2_struct_0(B_907) | k9_tmap_1('#skF_3', B_908)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_908, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_14136])).
% 35.70/24.51  tff(c_14145, plain, (![B_909]: (v2_struct_0(B_909) | k9_tmap_1('#skF_3', B_909)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_909, '#skF_3'))), inference(splitLeft, [status(thm)], [c_14137])).
% 35.70/24.51  tff(c_14147, plain, (v2_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_14145])).
% 35.70/24.51  tff(c_14150, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_14147])).
% 35.70/24.51  tff(c_293, plain, (![B_84, A_82, D_176]: (r1_tmap_1(B_84, k6_tmap_1(A_82, u1_struct_0(B_84)), k2_tmap_1(A_82, k6_tmap_1(A_82, u1_struct_0(B_84)), k6_partfun1(u1_struct_0(A_82)), B_84), D_176) | ~m1_subset_1(D_176, u1_struct_0(B_84)) | ~m1_pre_topc(B_84, A_82) | v2_struct_0(B_84) | ~m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82) | ~m1_pre_topc(B_84, A_82) | ~l1_pre_topc(A_82))), inference(superposition, [status(thm), theory('equality')], [c_77, c_275])).
% 35.70/24.51  tff(c_14241, plain, (![B_84, D_176]: (r1_tmap_1(B_84, k6_tmap_1('#skF_3', u1_struct_0(B_84)), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_84)), k9_tmap_1('#skF_3', '#skF_4'), B_84), D_176) | ~m1_subset_1(D_176, u1_struct_0(B_84)) | ~m1_pre_topc(B_84, '#skF_3') | v2_struct_0(B_84) | ~m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14150, c_293])).
% 35.70/24.51  tff(c_14301, plain, (![B_84, D_176]: (r1_tmap_1(B_84, k6_tmap_1('#skF_3', u1_struct_0(B_84)), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_84)), k9_tmap_1('#skF_3', '#skF_4'), B_84), D_176) | ~m1_subset_1(D_176, u1_struct_0(B_84)) | v2_struct_0(B_84) | ~m1_subset_1(u1_struct_0(B_84), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_84, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_58, c_56, c_14241])).
% 35.70/24.51  tff(c_15672, plain, (![B_979, D_980]: (r1_tmap_1(B_979, k6_tmap_1('#skF_3', u1_struct_0(B_979)), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_979)), k9_tmap_1('#skF_3', '#skF_4'), B_979), D_980) | ~m1_subset_1(D_980, u1_struct_0(B_979)) | v2_struct_0(B_979) | ~m1_subset_1(u1_struct_0(B_979), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_979, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_14301])).
% 35.70/24.51  tff(c_15676, plain, (![B_59, D_980]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_59)), k9_tmap_1('#skF_3', '#skF_4'), B_59), D_980) | ~m1_subset_1(D_980, u1_struct_0(B_59)) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_252, c_15672])).
% 35.70/24.51  tff(c_15688, plain, (![B_59, D_980]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_59)), k9_tmap_1('#skF_3', '#skF_4'), B_59), D_980) | ~m1_subset_1(D_980, u1_struct_0(B_59)) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_15676])).
% 35.70/24.51  tff(c_15693, plain, (![B_981, D_982]: (r1_tmap_1(B_981, k8_tmap_1('#skF_3', B_981), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', u1_struct_0(B_981)), k9_tmap_1('#skF_3', '#skF_4'), B_981), D_982) | ~m1_subset_1(D_982, u1_struct_0(B_981)) | v2_struct_0(B_981) | ~m1_subset_1(u1_struct_0(B_981), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_981, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_15688])).
% 35.70/24.51  tff(c_15697, plain, (![B_59, D_982]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_59), k9_tmap_1('#skF_3', '#skF_4'), B_59), D_982) | ~m1_subset_1(D_982, u1_struct_0(B_59)) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_252, c_15693])).
% 35.70/24.51  tff(c_15702, plain, (![B_59, D_982]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_59), k9_tmap_1('#skF_3', '#skF_4'), B_59), D_982) | ~m1_subset_1(D_982, u1_struct_0(B_59)) | v2_struct_0(B_59) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_15697])).
% 35.70/24.51  tff(c_15704, plain, (![B_983, D_984]: (r1_tmap_1(B_983, k8_tmap_1('#skF_3', B_983), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_983), k9_tmap_1('#skF_3', '#skF_4'), B_983), D_984) | ~m1_subset_1(D_984, u1_struct_0(B_983)) | v2_struct_0(B_983) | ~m1_subset_1(u1_struct_0(B_983), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_983, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_15702])).
% 35.70/24.51  tff(c_15707, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_15704, c_48])).
% 35.70/24.51  tff(c_15710, plain, (v2_struct_0('#skF_4') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_15707])).
% 35.70/24.51  tff(c_15711, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_15710])).
% 35.70/24.51  tff(c_15714, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_15711])).
% 35.70/24.51  tff(c_15718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_15714])).
% 35.70/24.51  tff(c_15719, plain, (![B_907]: (m1_subset_1(u1_struct_0(B_907), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k9_tmap_1('#skF_3', B_907)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_907, '#skF_3') | v2_struct_0(B_907))), inference(splitRight, [status(thm)], [c_14137])).
% 35.70/24.51  tff(c_33941, plain, (![B_1096]: (k7_tmap_1('#skF_3', u1_struct_0(B_1096))=k6_partfun1(u1_struct_0('#skF_3')) | k7_tmap_1('#skF_3', u1_struct_0(B_1096))=k9_tmap_1('#skF_3', B_1096) | v2_struct_0(B_1096) | '#skF_2'('#skF_3', B_1096, k9_tmap_1('#skF_3', B_1096))=u1_struct_0(B_1096) | ~m1_pre_topc(B_1096, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_33927])).
% 35.70/24.51  tff(c_34309, plain, (![B_1096, D_176]: (r1_tmap_1(B_1096, k6_tmap_1('#skF_3', u1_struct_0(B_1096)), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_1096), k9_tmap_1('#skF_3', B_1096), B_1096), D_176) | ~m1_subset_1(D_176, u1_struct_0(B_1096)) | ~m1_pre_topc(B_1096, '#skF_3') | v2_struct_0(B_1096) | ~m1_subset_1(u1_struct_0(B_1096), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_1096, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | k7_tmap_1('#skF_3', u1_struct_0(B_1096))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0(B_1096) | '#skF_2'('#skF_3', B_1096, k9_tmap_1('#skF_3', B_1096))=u1_struct_0(B_1096) | ~m1_pre_topc(B_1096, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33941, c_281])).
% 35.70/24.51  tff(c_34883, plain, (![B_1096, D_176]: (r1_tmap_1(B_1096, k6_tmap_1('#skF_3', u1_struct_0(B_1096)), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_1096), k9_tmap_1('#skF_3', B_1096), B_1096), D_176) | ~m1_subset_1(D_176, u1_struct_0(B_1096)) | ~m1_subset_1(u1_struct_0(B_1096), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | k7_tmap_1('#skF_3', u1_struct_0(B_1096))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0(B_1096) | '#skF_2'('#skF_3', B_1096, k9_tmap_1('#skF_3', B_1096))=u1_struct_0(B_1096) | ~m1_pre_topc(B_1096, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_58, c_56, c_34309])).
% 35.70/24.51  tff(c_73736, plain, (![B_1275, D_1276]: (r1_tmap_1(B_1275, k6_tmap_1('#skF_3', u1_struct_0(B_1275)), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_1275), k9_tmap_1('#skF_3', B_1275), B_1275), D_1276) | ~m1_subset_1(D_1276, u1_struct_0(B_1275)) | ~m1_subset_1(u1_struct_0(B_1275), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k7_tmap_1('#skF_3', u1_struct_0(B_1275))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0(B_1275) | '#skF_2'('#skF_3', B_1275, k9_tmap_1('#skF_3', B_1275))=u1_struct_0(B_1275) | ~m1_pre_topc(B_1275, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_34883])).
% 35.70/24.51  tff(c_73794, plain, (![B_59, D_1276]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_59), k9_tmap_1('#skF_3', B_59), B_59), D_1276) | ~m1_subset_1(D_1276, u1_struct_0(B_59)) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k7_tmap_1('#skF_3', u1_struct_0(B_59))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0(B_59) | '#skF_2'('#skF_3', B_59, k9_tmap_1('#skF_3', B_59))=u1_struct_0(B_59) | ~m1_pre_topc(B_59, '#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_252, c_73736])).
% 35.70/24.51  tff(c_73799, plain, (![B_59, D_1276]: (r1_tmap_1(B_59, k8_tmap_1('#skF_3', B_59), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_59), k9_tmap_1('#skF_3', B_59), B_59), D_1276) | ~m1_subset_1(D_1276, u1_struct_0(B_59)) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k7_tmap_1('#skF_3', u1_struct_0(B_59))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0(B_59) | '#skF_2'('#skF_3', B_59, k9_tmap_1('#skF_3', B_59))=u1_struct_0(B_59) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_73794])).
% 35.70/24.51  tff(c_73801, plain, (![B_1277, D_1278]: (r1_tmap_1(B_1277, k8_tmap_1('#skF_3', B_1277), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', B_1277), k9_tmap_1('#skF_3', B_1277), B_1277), D_1278) | ~m1_subset_1(D_1278, u1_struct_0(B_1277)) | ~m1_subset_1(u1_struct_0(B_1277), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k7_tmap_1('#skF_3', u1_struct_0(B_1277))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0(B_1277) | '#skF_2'('#skF_3', B_1277, k9_tmap_1('#skF_3', B_1277))=u1_struct_0(B_1277) | ~m1_pre_topc(B_1277, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_73799])).
% 35.70/24.51  tff(c_73804, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_4') | '#skF_2'('#skF_3', '#skF_4', k9_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_73801, c_48])).
% 35.70/24.51  tff(c_73861, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_4') | '#skF_2'('#skF_3', '#skF_4', k9_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_73804])).
% 35.70/24.51  tff(c_73862, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k6_partfun1(u1_struct_0('#skF_3')) | '#skF_2'('#skF_3', '#skF_4', k9_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_73861])).
% 35.70/24.51  tff(c_73863, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_73862])).
% 35.70/24.51  tff(c_73877, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_15719, c_73863])).
% 35.70/24.51  tff(c_73883, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_73877])).
% 35.70/24.51  tff(c_73885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_52064, c_73883])).
% 35.70/24.51  tff(c_73887, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_73862])).
% 35.70/24.51  tff(c_73896, plain, (k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k6_partfun1(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_73887, c_10])).
% 35.70/24.51  tff(c_73914, plain, (k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k6_partfun1(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_73896])).
% 35.70/24.51  tff(c_73915, plain, (k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k6_partfun1(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_73914])).
% 35.70/24.51  tff(c_74238, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73915, c_265])).
% 35.70/24.51  tff(c_74501, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_58, c_56, c_73887, c_74238])).
% 35.70/24.51  tff(c_74502, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_74501])).
% 35.70/24.51  tff(c_74235, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73915, c_262])).
% 35.70/24.51  tff(c_74498, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_58, c_56, c_73887, c_74235])).
% 35.70/24.51  tff(c_74499, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')))))), inference(negUnitSimplification, [status(thm)], [c_60, c_74498])).
% 35.70/24.51  tff(c_75042, plain, (![A_3, B_4]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), A_3, B_4) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | v1_xboole_0(B_4))), inference(resolution, [status(thm)], [c_74499, c_6])).
% 35.70/24.51  tff(c_75063, plain, (![A_3, B_4]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), A_3, B_4) | v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | v1_xboole_0(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_74502, c_75042])).
% 35.70/24.51  tff(c_76708, plain, (v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_75063])).
% 35.70/24.51  tff(c_76714, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_76708])).
% 35.70/24.51  tff(c_76717, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_76714])).
% 35.70/24.51  tff(c_76719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_996, c_76717])).
% 35.70/24.51  tff(c_76721, plain, (~v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_75063])).
% 35.70/24.51  tff(c_74247, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4')))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73915, c_30])).
% 35.70/24.51  tff(c_74510, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4')))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_73887, c_74247])).
% 35.70/24.51  tff(c_74511, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_74510])).
% 35.70/24.51  tff(c_74244, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4')))))) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73915, c_28])).
% 35.70/24.51  tff(c_74507, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4')))))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_73887, c_74244])).
% 35.70/24.51  tff(c_74508, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))))))), inference(negUnitSimplification, [status(thm)], [c_60, c_74507])).
% 35.70/24.51  tff(c_75082, plain, (![A_3, B_4]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4')))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), A_3, B_4) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4')))) | v1_xboole_0(B_4))), inference(resolution, [status(thm)], [c_74508, c_6])).
% 35.70/24.51  tff(c_75095, plain, (![A_3, B_4]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), A_3, B_4) | v1_xboole_0(u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4')))) | v1_xboole_0(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_74511, c_75082])).
% 35.70/24.51  tff(c_79874, plain, (v1_xboole_0(u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_75095])).
% 35.70/24.51  tff(c_79903, plain, (v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_252, c_79874])).
% 35.70/24.51  tff(c_79906, plain, (v1_xboole_0(u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_79903])).
% 35.70/24.51  tff(c_79908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_76721, c_79906])).
% 35.70/24.51  tff(c_79909, plain, (![A_3, B_4]: (r1_funct_2(A_3, B_4, u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), A_3, B_4) | v1_xboole_0(B_4))), inference(splitRight, [status(thm)], [c_75095])).
% 35.70/24.51  tff(c_2890, plain, (![B_232]: ('#skF_2'('#skF_3', B_232, k7_tmap_1('#skF_3', u1_struct_0(B_232)))=u1_struct_0(B_232) | k7_tmap_1('#skF_3', u1_struct_0(B_232))=k9_tmap_1('#skF_3', B_232) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_232, '#skF_3') | ~l1_pre_topc('#skF_3') | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_2884])).
% 35.70/24.51  tff(c_2905, plain, (![B_232]: ('#skF_2'('#skF_3', B_232, k7_tmap_1('#skF_3', u1_struct_0(B_232)))=u1_struct_0(B_232) | k7_tmap_1('#skF_3', u1_struct_0(B_232))=k9_tmap_1('#skF_3', B_232) | v2_struct_0('#skF_3') | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_141, c_2890])).
% 35.70/24.51  tff(c_2906, plain, (![B_232]: ('#skF_2'('#skF_3', B_232, k7_tmap_1('#skF_3', u1_struct_0(B_232)))=u1_struct_0(B_232) | k7_tmap_1('#skF_3', u1_struct_0(B_232))=k9_tmap_1('#skF_3', B_232) | k9_tmap_1('#skF_3', B_232)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_232, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_2905])).
% 35.70/24.51  tff(c_74199, plain, ('#skF_2'('#skF_3', '#skF_4', k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0('#skF_4') | k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k9_tmap_1('#skF_3', '#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73915, c_2906])).
% 35.70/24.51  tff(c_74461, plain, ('#skF_2'('#skF_3', '#skF_4', k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_73915, c_74199])).
% 35.70/24.51  tff(c_74462, plain, ('#skF_2'('#skF_3', '#skF_4', k6_partfun1(u1_struct_0('#skF_3')))=u1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52064, c_74461])).
% 35.70/24.51  tff(c_467, plain, (![A_216, B_217, C_218]: (~r1_funct_2(u1_struct_0(A_216), u1_struct_0(k8_tmap_1(A_216, B_217)), u1_struct_0(A_216), u1_struct_0(k6_tmap_1(A_216, '#skF_2'(A_216, B_217, C_218))), C_218, k7_tmap_1(A_216, '#skF_2'(A_216, B_217, C_218))) | k9_tmap_1(A_216, B_217)=C_218 | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_216), u1_struct_0(k8_tmap_1(A_216, B_217))))) | ~v1_funct_2(C_218, u1_struct_0(A_216), u1_struct_0(k8_tmap_1(A_216, B_217))) | ~v1_funct_1(C_218) | ~m1_pre_topc(B_217, A_216) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_123])).
% 35.70/24.51  tff(c_473, plain, (![A_75, B_79, C_218]: (~r1_funct_2(u1_struct_0(A_75), u1_struct_0(A_75), u1_struct_0(A_75), u1_struct_0(k6_tmap_1(A_75, '#skF_2'(A_75, B_79, C_218))), C_218, k7_tmap_1(A_75, '#skF_2'(A_75, B_79, C_218))) | k9_tmap_1(A_75, B_79)=C_218 | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_75), u1_struct_0(k8_tmap_1(A_75, B_79))))) | ~v1_funct_2(C_218, u1_struct_0(A_75), u1_struct_0(k8_tmap_1(A_75, B_79))) | ~v1_funct_1(C_218) | ~m1_pre_topc(B_79, A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75) | ~m1_pre_topc(B_79, A_75) | v2_struct_0(B_79) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_44, c_467])).
% 35.70/24.51  tff(c_74668, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))), k6_partfun1(u1_struct_0('#skF_3')), k7_tmap_1('#skF_3', '#skF_2'('#skF_3', '#skF_4', k6_partfun1(u1_struct_0('#skF_3'))))) | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4') | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_74462, c_473])).
% 35.70/24.51  tff(c_74875, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4') | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_58, c_56, c_52, c_141, c_73915, c_74462, c_74668])).
% 35.70/24.51  tff(c_74876, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4'))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_52064, c_74875])).
% 35.70/24.51  tff(c_84180, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', u1_struct_0('#skF_4'))), k6_partfun1(u1_struct_0('#skF_3')), k6_partfun1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74502, c_74499, c_74876])).
% 35.70/24.51  tff(c_84183, plain, (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_79909, c_84180])).
% 35.70/24.51  tff(c_84203, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_917, c_84183])).
% 35.70/24.51  tff(c_84205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_996, c_84203])).
% 35.70/24.51  tff(c_84206, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | '#skF_2'('#skF_3', '#skF_4', k9_tmap_1('#skF_3', '#skF_4'))=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_52063])).
% 35.70/24.51  tff(c_84965, plain, (~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_84206])).
% 35.70/24.51  tff(c_84968, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_46, c_84965])).
% 35.70/24.51  tff(c_84972, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_84968])).
% 35.70/24.51  tff(c_84974, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_84206])).
% 35.70/24.51  tff(c_84207, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52063])).
% 35.70/24.51  tff(c_84983, plain, (k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k6_partfun1(u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_84974, c_10])).
% 35.70/24.51  tff(c_85001, plain, (k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k9_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_84207, c_84983])).
% 35.70/24.51  tff(c_85002, plain, (k7_tmap_1('#skF_3', u1_struct_0('#skF_4'))=k9_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_85001])).
% 35.70/24.51  tff(c_85115, plain, (![D_176]: (r1_tmap_1('#skF_4', k6_tmap_1('#skF_3', u1_struct_0('#skF_4')), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', '#skF_4'), k9_tmap_1('#skF_3', '#skF_4'), '#skF_4'), D_176) | ~m1_subset_1(D_176, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_85002, c_281])).
% 35.70/24.51  tff(c_85209, plain, (![D_176]: (r1_tmap_1('#skF_4', k6_tmap_1('#skF_3', u1_struct_0('#skF_4')), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', '#skF_4'), k9_tmap_1('#skF_3', '#skF_4'), '#skF_4'), D_176) | ~m1_subset_1(D_176, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_58, c_56, c_84974, c_52, c_85115])).
% 35.70/24.51  tff(c_85847, plain, (![D_1353]: (r1_tmap_1('#skF_4', k6_tmap_1('#skF_3', u1_struct_0('#skF_4')), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', '#skF_4'), k9_tmap_1('#skF_3', '#skF_4'), '#skF_4'), D_1353) | ~m1_subset_1(D_1353, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_85209])).
% 35.70/24.51  tff(c_85850, plain, (![D_1353]: (r1_tmap_1('#skF_4', k8_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', '#skF_4'), k9_tmap_1('#skF_3', '#skF_4'), '#skF_4'), D_1353) | ~m1_subset_1(D_1353, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_252, c_85847])).
% 35.70/24.51  tff(c_85852, plain, (![D_1353]: (r1_tmap_1('#skF_4', k8_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', '#skF_4'), k9_tmap_1('#skF_3', '#skF_4'), '#skF_4'), D_1353) | ~m1_subset_1(D_1353, u1_struct_0('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_85850])).
% 35.70/24.51  tff(c_85854, plain, (![D_1354]: (r1_tmap_1('#skF_4', k8_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k8_tmap_1('#skF_3', '#skF_4'), k9_tmap_1('#skF_3', '#skF_4'), '#skF_4'), D_1354) | ~m1_subset_1(D_1354, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_85852])).
% 35.70/24.51  tff(c_85857, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_85854, c_48])).
% 35.70/24.51  tff(c_85861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_85857])).
% 35.70/24.51  tff(c_85864, plain, (![B_1355]: (~m1_subset_1(u1_struct_0(B_1355), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_1355) | k9_tmap_1('#skF_3', B_1355)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_1355, '#skF_3'))), inference(splitRight, [status(thm)], [c_863])).
% 35.70/24.51  tff(c_85871, plain, (![B_84]: (v2_struct_0(B_84) | k9_tmap_1('#skF_3', B_84)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_85864])).
% 35.70/24.51  tff(c_85875, plain, (![B_1356]: (v2_struct_0(B_1356) | k9_tmap_1('#skF_3', B_1356)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_1356, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_85871])).
% 35.70/24.51  tff(c_85877, plain, (v2_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_85875])).
% 35.70/24.51  tff(c_85880, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_85877])).
% 35.70/24.51  tff(c_85863, plain, (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_863])).
% 35.70/24.51  tff(c_85882, plain, (~m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_85880, c_85863])).
% 35.70/24.51  tff(c_336, plain, (![A_58, B_59]: (m1_subset_1(k6_partfun1(u1_struct_0(A_58)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_58), u1_struct_0(k8_tmap_1(A_58, B_59))))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~m1_pre_topc(B_59, A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_252, c_331])).
% 35.70/24.51  tff(c_85906, plain, (![B_59]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_59, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_85880, c_336])).
% 35.70/24.51  tff(c_85931, plain, (![B_59]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_59))))) | ~m1_subset_1(u1_struct_0(B_59), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_59, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_56, c_58, c_58, c_56, c_85906])).
% 35.70/24.51  tff(c_86118, plain, (![B_1370]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_1370))))) | ~m1_subset_1(u1_struct_0(B_1370), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_1370, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_85931])).
% 35.70/24.51  tff(c_86130, plain, (![B_79]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_79, '#skF_3') | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_86118])).
% 35.70/24.51  tff(c_86143, plain, (![B_79]: (m1_subset_1(k9_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')))) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_86130])).
% 35.70/24.51  tff(c_86145, plain, (![B_1371]: (~m1_subset_1(u1_struct_0(B_1371), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_1371, '#skF_3') | v2_struct_0(B_1371))), inference(negUnitSimplification, [status(thm)], [c_60, c_85882, c_86143])).
% 35.70/24.51  tff(c_86152, plain, (![B_84]: (v2_struct_0(B_84) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_86145])).
% 35.70/24.51  tff(c_86156, plain, (![B_1372]: (v2_struct_0(B_1372) | ~m1_pre_topc(B_1372, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_86152])).
% 35.70/24.51  tff(c_86159, plain, (v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_86156])).
% 35.70/24.51  tff(c_86163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_86159])).
% 35.70/24.51  tff(c_86174, plain, (![B_1374]: (~m1_subset_1(u1_struct_0(B_1374), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0(B_1374) | k9_tmap_1('#skF_3', B_1374)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_1374, '#skF_3'))), inference(splitRight, [status(thm)], [c_869])).
% 35.70/24.51  tff(c_86181, plain, (![B_84]: (v2_struct_0(B_84) | k9_tmap_1('#skF_3', B_84)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_86174])).
% 35.70/24.51  tff(c_86185, plain, (![B_1375]: (v2_struct_0(B_1375) | k9_tmap_1('#skF_3', B_1375)=k6_partfun1(u1_struct_0('#skF_3')) | ~m1_pre_topc(B_1375, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_86181])).
% 35.70/24.51  tff(c_86187, plain, (v2_struct_0('#skF_4') | k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_86185])).
% 35.70/24.51  tff(c_86190, plain, (k6_partfun1(u1_struct_0('#skF_3'))=k9_tmap_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_86187])).
% 35.70/24.51  tff(c_86165, plain, (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_869])).
% 35.70/24.51  tff(c_86192, plain, (~v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86190, c_86165])).
% 35.70/24.51  tff(c_86217, plain, (![B_170]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_170))) | ~m1_subset_1(u1_struct_0(B_170), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_170, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_170, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_86190, c_259])).
% 35.70/24.51  tff(c_86242, plain, (![B_170]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_170))) | ~m1_subset_1(u1_struct_0(B_170), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_170, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_56, c_58, c_58, c_56, c_86217])).
% 35.70/24.51  tff(c_86278, plain, (![B_1381]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k8_tmap_1('#skF_3', B_1381))) | ~m1_subset_1(u1_struct_0(B_1381), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_1381, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_86242])).
% 35.70/24.51  tff(c_86282, plain, (![B_79]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_79, '#skF_3') | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_86278])).
% 35.70/24.51  tff(c_86284, plain, (![B_79]: (v1_funct_2(k9_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~m1_subset_1(u1_struct_0(B_79), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_79, '#skF_3') | v2_struct_0(B_79) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_86282])).
% 35.70/24.51  tff(c_86286, plain, (![B_1382]: (~m1_subset_1(u1_struct_0(B_1382), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_1382, '#skF_3') | v2_struct_0(B_1382))), inference(negUnitSimplification, [status(thm)], [c_60, c_86192, c_86284])).
% 35.70/24.51  tff(c_86293, plain, (![B_84]: (v2_struct_0(B_84) | ~m1_pre_topc(B_84, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_86286])).
% 35.70/24.51  tff(c_86297, plain, (![B_1383]: (v2_struct_0(B_1383) | ~m1_pre_topc(B_1383, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_86293])).
% 35.70/24.51  tff(c_86300, plain, (v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_86297])).
% 35.70/24.51  tff(c_86304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_86300])).
% 35.70/24.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.70/24.51  
% 35.70/24.51  Inference rules
% 35.70/24.51  ----------------------
% 35.70/24.51  #Ref     : 0
% 35.70/24.51  #Sup     : 21187
% 35.70/24.51  #Fact    : 40
% 35.70/24.51  #Define  : 0
% 35.70/24.51  #Split   : 32
% 35.70/24.51  #Chain   : 0
% 35.70/24.51  #Close   : 0
% 35.70/24.51  
% 35.70/24.51  Ordering : KBO
% 35.70/24.51  
% 35.70/24.51  Simplification rules
% 35.70/24.51  ----------------------
% 35.70/24.51  #Subsume      : 6743
% 35.70/24.51  #Demod        : 15111
% 35.70/24.51  #Tautology    : 7394
% 35.70/24.51  #SimpNegUnit  : 4525
% 35.70/24.51  #BackRed      : 403
% 35.70/24.51  
% 35.70/24.51  #Partial instantiations: 0
% 35.70/24.51  #Strategies tried      : 1
% 35.70/24.51  
% 35.70/24.51  Timing (in seconds)
% 35.70/24.51  ----------------------
% 35.70/24.52  Preprocessing        : 0.38
% 35.70/24.52  Parsing              : 0.20
% 35.70/24.52  CNF conversion       : 0.03
% 35.70/24.52  Main loop            : 23.26
% 35.70/24.52  Inferencing          : 4.49
% 35.70/24.52  Reduction            : 4.21
% 35.70/24.52  Demodulation         : 2.73
% 35.70/24.52  BG Simplification    : 0.63
% 35.70/24.52  Subsumption          : 13.24
% 35.70/24.52  Abstraction          : 1.23
% 35.70/24.52  MUC search           : 0.00
% 35.70/24.52  Cooper               : 0.00
% 35.70/24.52  Total                : 23.73
% 35.70/24.52  Index Insertion      : 0.00
% 35.70/24.52  Index Deletion       : 0.00
% 35.70/24.52  Index Matching       : 0.00
% 35.70/24.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
