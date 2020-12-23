%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:01 EST 2020

% Result     : Theorem 16.82s
% Output     : CNFRefutation 16.95s
% Verified   : 
% Statistics : Number of formulae       :  160 (1084 expanded)
%              Number of leaves         :   45 ( 403 expanded)
%              Depth                    :   49
%              Number of atoms          :  699 (5313 expanded)
%              Number of equality atoms :   63 ( 375 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_219,negated_conjecture,(
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

tff(f_200,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_156,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_100,axiom,(
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

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k7_tmap_1(A,B) = k6_partfun1(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_62,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] : m1_pre_topc(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_pre_topc)).

tff(f_126,axiom,(
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

tff(f_193,axiom,(
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

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_46,plain,(
    ! [B_82,A_80] :
      ( m1_subset_1(u1_struct_0(B_82),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_34,plain,(
    ! [A_60,B_61] :
      ( l1_pre_topc(k8_tmap_1(A_60,B_61))
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    ! [A_60,B_61] :
      ( v1_pre_topc(k8_tmap_1(A_60,B_61))
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_36,plain,(
    ! [A_60,B_61] :
      ( v2_pre_topc(k8_tmap_1(A_60,B_61))
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_302,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_543,plain,(
    ! [A_167,B_168] :
      ( k6_tmap_1(A_167,u1_struct_0(B_168)) = k8_tmap_1(A_167,B_168)
      | ~ l1_pre_topc(k8_tmap_1(A_167,B_168))
      | ~ v2_pre_topc(k8_tmap_1(A_167,B_168))
      | ~ v1_pre_topc(k8_tmap_1(A_167,B_168))
      | ~ v2_pre_topc(A_167)
      | v2_struct_0(A_167)
      | ~ m1_pre_topc(B_168,A_167)
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_46,c_302])).

tff(c_548,plain,(
    ! [A_169,B_170] :
      ( k6_tmap_1(A_169,u1_struct_0(B_170)) = k8_tmap_1(A_169,B_170)
      | ~ l1_pre_topc(k8_tmap_1(A_169,B_170))
      | ~ v1_pre_topc(k8_tmap_1(A_169,B_170))
      | ~ m1_pre_topc(B_170,A_169)
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_36,c_543])).

tff(c_553,plain,(
    ! [A_171,B_172] :
      ( k6_tmap_1(A_171,u1_struct_0(B_172)) = k8_tmap_1(A_171,B_172)
      | ~ l1_pre_topc(k8_tmap_1(A_171,B_172))
      | ~ m1_pre_topc(B_172,A_171)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_38,c_548])).

tff(c_557,plain,(
    ! [A_60,B_61] :
      ( k6_tmap_1(A_60,u1_struct_0(B_61)) = k8_tmap_1(A_60,B_61)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_34,c_553])).

tff(c_73,plain,(
    ! [A_100,B_101] :
      ( u1_struct_0(k6_tmap_1(A_100,B_101)) = u1_struct_0(A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_77,plain,(
    ! [A_80,B_82] :
      ( u1_struct_0(k6_tmap_1(A_80,u1_struct_0(B_82))) = u1_struct_0(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_112,plain,(
    ! [A_106,B_107] :
      ( k7_tmap_1(A_106,B_107) = k6_partfun1(u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_119,plain,(
    ! [A_80,B_82] :
      ( k7_tmap_1(A_80,u1_struct_0(B_82)) = k6_partfun1(u1_struct_0(A_80))
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_46,c_112])).

tff(c_155,plain,(
    ! [A_114,B_115] :
      ( v1_funct_2(k7_tmap_1(A_114,B_115),u1_struct_0(A_114),u1_struct_0(k6_tmap_1(A_114,B_115)))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1074,plain,(
    ! [A_222,B_223] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_222)),u1_struct_0(A_222),u1_struct_0(k6_tmap_1(A_222,u1_struct_0(B_223))))
      | ~ m1_subset_1(u1_struct_0(B_223),k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222)
      | ~ m1_pre_topc(B_223,A_222)
      | ~ l1_pre_topc(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_155])).

tff(c_4188,plain,(
    ! [A_396,B_397] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_396)),u1_struct_0(A_396),u1_struct_0(A_396))
      | ~ m1_subset_1(u1_struct_0(B_397),k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396)
      | ~ m1_pre_topc(B_397,A_396)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396)
      | ~ m1_pre_topc(B_397,A_396)
      | ~ l1_pre_topc(A_396) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1074])).

tff(c_4254,plain,(
    ! [A_398,B_399] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_398)),u1_struct_0(A_398),u1_struct_0(A_398))
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398)
      | ~ m1_pre_topc(B_399,A_398)
      | ~ l1_pre_topc(A_398) ) ),
    inference(resolution,[status(thm)],[c_46,c_4188])).

tff(c_4258,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_4254])).

tff(c_4262,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_4258])).

tff(c_4263,plain,(
    v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4262])).

tff(c_568,plain,(
    ! [A_176,B_177] :
      ( k6_tmap_1(A_176,u1_struct_0(B_177)) = k8_tmap_1(A_176,B_177)
      | ~ m1_pre_topc(B_177,A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_34,c_553])).

tff(c_609,plain,(
    ! [A_176,B_177] :
      ( u1_struct_0(k8_tmap_1(A_176,B_177)) = u1_struct_0(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176)
      | ~ m1_pre_topc(B_177,A_176)
      | ~ l1_pre_topc(A_176)
      | ~ m1_pre_topc(B_177,A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_77])).

tff(c_179,plain,(
    ! [A_120,B_121] :
      ( m1_subset_1(k7_tmap_1(A_120,B_121),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120),u1_struct_0(k6_tmap_1(A_120,B_121)))))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1974,plain,(
    ! [A_277,B_278] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_277)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_277),u1_struct_0(k6_tmap_1(A_277,u1_struct_0(B_278))))))
      | ~ m1_subset_1(u1_struct_0(B_278),k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277)
      | ~ m1_pre_topc(B_278,A_277)
      | ~ l1_pre_topc(A_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_179])).

tff(c_7150,plain,(
    ! [A_460,B_461] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_460)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_460),u1_struct_0(A_460))))
      | ~ m1_subset_1(u1_struct_0(B_461),k1_zfmisc_1(u1_struct_0(A_460)))
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460)
      | ~ m1_pre_topc(B_461,A_460)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460)
      | ~ m1_pre_topc(B_461,A_460)
      | ~ l1_pre_topc(A_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1974])).

tff(c_7231,plain,(
    ! [A_462,B_463] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_462)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_462),u1_struct_0(A_462))))
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462)
      | ~ m1_pre_topc(B_463,A_462)
      | ~ l1_pre_topc(A_462) ) ),
    inference(resolution,[status(thm)],[c_46,c_7150])).

tff(c_7235,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_7231])).

tff(c_7239,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_7235])).

tff(c_7240,plain,(
    m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7239])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_128,plain,(
    ! [A_110,B_111] :
      ( k7_tmap_1(A_110,u1_struct_0(B_111)) = k6_partfun1(u1_struct_0(A_110))
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110)
      | ~ m1_pre_topc(B_111,A_110)
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_46,c_112])).

tff(c_68,plain,(
    ! [A_98,B_99] :
      ( v1_funct_1(k7_tmap_1(A_98,B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_72,plain,(
    ! [A_80,B_82] :
      ( v1_funct_1(k7_tmap_1(A_80,u1_struct_0(B_82)))
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_46,c_68])).

tff(c_169,plain,(
    ! [A_118,B_119] :
      ( v1_funct_1(k6_partfun1(u1_struct_0(A_118)))
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118)
      | ~ m1_pre_topc(B_119,A_118)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118)
      | ~ m1_pre_topc(B_119,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_72])).

tff(c_173,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0('#skF_4')))
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_169])).

tff(c_177,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_58,c_173])).

tff(c_178,plain,(
    v1_funct_1(k6_partfun1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_177])).

tff(c_8,plain,(
    ! [B_6,C_7,E_9,D_8,A_5,F_10] :
      ( r1_funct_2(A_5,B_6,C_7,D_8,E_9,E_9)
      | ~ m1_subset_1(F_10,k1_zfmisc_1(k2_zfmisc_1(C_7,D_8)))
      | ~ v1_funct_2(F_10,C_7,D_8)
      | ~ v1_funct_1(F_10)
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(E_9,A_5,B_6)
      | ~ v1_funct_1(E_9)
      | v1_xboole_0(D_8)
      | v1_xboole_0(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7242,plain,(
    ! [A_5,B_6,E_9] :
      ( r1_funct_2(A_5,B_6,u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),E_9,E_9)
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(E_9,A_5,B_6)
      | ~ v1_funct_1(E_9)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_6) ) ),
    inference(resolution,[status(thm)],[c_7240,c_8])).

tff(c_7245,plain,(
    ! [A_5,B_6,E_9] :
      ( r1_funct_2(A_5,B_6,u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),E_9,E_9)
      | ~ m1_subset_1(E_9,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(E_9,A_5,B_6)
      | ~ v1_funct_1(E_9)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_4263,c_7242])).

tff(c_7484,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7245])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(u1_struct_0(A_4))
      | ~ l1_struct_0(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_7487,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7484,c_6])).

tff(c_7490,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7487])).

tff(c_7493,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_7490])).

tff(c_7497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7493])).

tff(c_7499,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7245])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_pre_topc('#skF_1'(A_2),A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4259,plain,(
    ! [A_2] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_2)),u1_struct_0(A_2),u1_struct_0(A_2))
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_4254])).

tff(c_7246,plain,(
    ! [A_464] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_464)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_464),u1_struct_0(A_464))))
      | ~ v2_pre_topc(A_464)
      | v2_struct_0(A_464)
      | ~ l1_pre_topc(A_464) ) ),
    inference(resolution,[status(thm)],[c_4,c_7231])).

tff(c_13125,plain,(
    ! [A_700,B_701,A_702,E_703] :
      ( r1_funct_2(A_700,B_701,u1_struct_0(A_702),u1_struct_0(A_702),E_703,E_703)
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_702)),u1_struct_0(A_702),u1_struct_0(A_702))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_702)))
      | ~ m1_subset_1(E_703,k1_zfmisc_1(k2_zfmisc_1(A_700,B_701)))
      | ~ v1_funct_2(E_703,A_700,B_701)
      | ~ v1_funct_1(E_703)
      | v1_xboole_0(u1_struct_0(A_702))
      | v1_xboole_0(B_701)
      | ~ v2_pre_topc(A_702)
      | v2_struct_0(A_702)
      | ~ l1_pre_topc(A_702) ) ),
    inference(resolution,[status(thm)],[c_7246,c_8])).

tff(c_13214,plain,(
    ! [A_700,B_701,A_2,E_703] :
      ( r1_funct_2(A_700,B_701,u1_struct_0(A_2),u1_struct_0(A_2),E_703,E_703)
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_2)))
      | ~ m1_subset_1(E_703,k1_zfmisc_1(k2_zfmisc_1(A_700,B_701)))
      | ~ v1_funct_2(E_703,A_700,B_701)
      | ~ v1_funct_1(E_703)
      | v1_xboole_0(u1_struct_0(A_2))
      | v1_xboole_0(B_701)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_4259,c_13125])).

tff(c_189,plain,(
    ! [A_122] :
      ( v1_funct_1(k6_partfun1(u1_struct_0(A_122)))
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122)
      | ~ m1_pre_topc('#skF_1'(A_122),A_122)
      | ~ l1_pre_topc(A_122) ) ),
    inference(resolution,[status(thm)],[c_4,c_169])).

tff(c_192,plain,(
    ! [A_2] :
      ( v1_funct_1(k6_partfun1(u1_struct_0(A_2)))
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_1086,plain,(
    ! [A_60,B_61] :
      ( v1_funct_2(k6_partfun1(u1_struct_0(A_60)),u1_struct_0(A_60),u1_struct_0(k8_tmap_1(A_60,B_61)))
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ m1_pre_topc(B_61,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_1074])).

tff(c_9168,plain,(
    ! [A_541,B_542] :
      ( m1_subset_1(k6_partfun1(u1_struct_0(A_541)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_541),u1_struct_0(k8_tmap_1(A_541,B_542)))))
      | ~ m1_subset_1(u1_struct_0(B_542),k1_zfmisc_1(u1_struct_0(A_541)))
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541)
      | ~ m1_pre_topc(B_542,A_541)
      | ~ l1_pre_topc(A_541)
      | ~ m1_pre_topc(B_542,A_541)
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_1974])).

tff(c_24,plain,(
    ! [B_48,A_36,C_54] :
      ( u1_struct_0(B_48) = '#skF_3'(A_36,B_48,C_54)
      | k9_tmap_1(A_36,B_48) = C_54
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)))))
      | ~ v1_funct_2(C_54,u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)))
      | ~ v1_funct_1(C_54)
      | ~ m1_pre_topc(B_48,A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10479,plain,(
    ! [A_602,B_603] :
      ( '#skF_3'(A_602,B_603,k6_partfun1(u1_struct_0(A_602))) = u1_struct_0(B_603)
      | k9_tmap_1(A_602,B_603) = k6_partfun1(u1_struct_0(A_602))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_602)),u1_struct_0(A_602),u1_struct_0(k8_tmap_1(A_602,B_603)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_602)))
      | ~ m1_subset_1(u1_struct_0(B_603),k1_zfmisc_1(u1_struct_0(A_602)))
      | ~ m1_pre_topc(B_603,A_602)
      | ~ l1_pre_topc(A_602)
      | ~ v2_pre_topc(A_602)
      | v2_struct_0(A_602) ) ),
    inference(resolution,[status(thm)],[c_9168,c_24])).

tff(c_10583,plain,(
    ! [A_604,B_605] :
      ( '#skF_3'(A_604,B_605,k6_partfun1(u1_struct_0(A_604))) = u1_struct_0(B_605)
      | k9_tmap_1(A_604,B_605) = k6_partfun1(u1_struct_0(A_604))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_604)))
      | ~ m1_subset_1(u1_struct_0(B_605),k1_zfmisc_1(u1_struct_0(A_604)))
      | ~ m1_pre_topc(B_605,A_604)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(resolution,[status(thm)],[c_1086,c_10479])).

tff(c_10664,plain,(
    ! [A_606,B_607] :
      ( '#skF_3'(A_606,B_607,k6_partfun1(u1_struct_0(A_606))) = u1_struct_0(B_607)
      | k9_tmap_1(A_606,B_607) = k6_partfun1(u1_struct_0(A_606))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_606)))
      | ~ v2_pre_topc(A_606)
      | v2_struct_0(A_606)
      | ~ m1_pre_topc(B_607,A_606)
      | ~ l1_pre_topc(A_606) ) ),
    inference(resolution,[status(thm)],[c_46,c_10583])).

tff(c_10697,plain,(
    ! [A_2,B_607] :
      ( '#skF_3'(A_2,B_607,k6_partfun1(u1_struct_0(A_2))) = u1_struct_0(B_607)
      | k9_tmap_1(A_2,B_607) = k6_partfun1(u1_struct_0(A_2))
      | ~ m1_pre_topc(B_607,A_2)
      | ~ v2_pre_topc(A_2)
      | v2_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_192,c_10664])).

tff(c_10694,plain,(
    ! [B_607] :
      ( '#skF_3'('#skF_4',B_607,k6_partfun1(u1_struct_0('#skF_4'))) = u1_struct_0(B_607)
      | k9_tmap_1('#skF_4',B_607) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_607,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_178,c_10664])).

tff(c_10700,plain,(
    ! [B_607] :
      ( '#skF_3'('#skF_4',B_607,k6_partfun1(u1_struct_0('#skF_4'))) = u1_struct_0(B_607)
      | k9_tmap_1('#skF_4',B_607) = k6_partfun1(u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_607,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_10694])).

tff(c_10702,plain,(
    ! [B_608] :
      ( '#skF_3'('#skF_4',B_608,k6_partfun1(u1_struct_0('#skF_4'))) = u1_struct_0(B_608)
      | k9_tmap_1('#skF_4',B_608) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_608,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_10700])).

tff(c_22,plain,(
    ! [A_36,B_48,C_54] :
      ( ~ r1_funct_2(u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)),u1_struct_0(A_36),u1_struct_0(k6_tmap_1(A_36,'#skF_3'(A_36,B_48,C_54))),C_54,k7_tmap_1(A_36,'#skF_3'(A_36,B_48,C_54)))
      | k9_tmap_1(A_36,B_48) = C_54
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)))))
      | ~ v1_funct_2(C_54,u1_struct_0(A_36),u1_struct_0(k8_tmap_1(A_36,B_48)))
      | ~ v1_funct_1(C_54)
      | ~ m1_pre_topc(B_48,A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_10708,plain,(
    ! [B_608] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_608)),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4',u1_struct_0(B_608))),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4','#skF_3'('#skF_4',B_608,k6_partfun1(u1_struct_0('#skF_4')))))
      | k9_tmap_1('#skF_4',B_608) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_608)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_608)))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_608,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | k9_tmap_1('#skF_4',B_608) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_608,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10702,c_22])).

tff(c_10717,plain,(
    ! [B_608] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_608)),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4',u1_struct_0(B_608))),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4','#skF_3'('#skF_4',B_608,k6_partfun1(u1_struct_0('#skF_4')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_608)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_608)))
      | v2_struct_0('#skF_4')
      | k9_tmap_1('#skF_4',B_608) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_608,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_178,c_10708])).

tff(c_11006,plain,(
    ! [B_620] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_620)),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4',u1_struct_0(B_620))),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4','#skF_3'('#skF_4',B_620,k6_partfun1(u1_struct_0('#skF_4')))))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_620)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_620)))
      | k9_tmap_1('#skF_4',B_620) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_620,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_10717])).

tff(c_11010,plain,(
    ! [B_607] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_607)),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4',u1_struct_0(B_607))),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_607)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_607)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_607)))
      | k9_tmap_1('#skF_4',B_607) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_607,'#skF_4')
      | k9_tmap_1('#skF_4',B_607) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_607,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10697,c_11006])).

tff(c_11113,plain,(
    ! [B_607] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_607)),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4',u1_struct_0(B_607))),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_607)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_607)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_607)))
      | k9_tmap_1('#skF_4',B_607) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_607,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_11010])).

tff(c_11617,plain,(
    ! [B_647] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_647)),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4',u1_struct_0(B_647))),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_647)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_647)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_647)))
      | k9_tmap_1('#skF_4',B_647) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_647,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11113])).

tff(c_11786,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_82)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))
      | k9_tmap_1('#skF_4',B_82) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_82,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_82,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_11617])).

tff(c_11854,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_82)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))
      | k9_tmap_1('#skF_4',B_82) = k6_partfun1(u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_82,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_11786])).

tff(c_12445,plain,(
    ! [B_675] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_675)),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_675)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_675)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_675)))
      | k9_tmap_1('#skF_4',B_675) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_675,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_11854])).

tff(c_12519,plain,(
    ! [B_177] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_177)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_177)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_177)))
      | k9_tmap_1('#skF_4',B_177) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_12445])).

tff(c_12571,plain,(
    ! [B_177] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_177)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_177)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_177)))
      | k9_tmap_1('#skF_4',B_177) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_177,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_56,c_58,c_12519])).

tff(c_13026,plain,(
    ! [B_699] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k7_tmap_1('#skF_4',u1_struct_0(B_699)))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_699)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_699)))
      | k9_tmap_1('#skF_4',B_699) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_699,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_12571])).

tff(c_13097,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k6_partfun1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))
      | k9_tmap_1('#skF_4',B_82) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_82,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_82,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_13026])).

tff(c_13123,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k6_partfun1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))
      | k9_tmap_1('#skF_4',B_82) = k6_partfun1(u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_82,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_13097])).

tff(c_13124,plain,(
    ! [B_82] :
      ( ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k6_partfun1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_82)))
      | k9_tmap_1('#skF_4',B_82) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_82,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13123])).

tff(c_13872,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'),k6_partfun1(u1_struct_0('#skF_4')),k6_partfun1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_13124])).

tff(c_13875,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_13214,c_13872])).

tff(c_13881,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_178,c_4263,c_7240,c_13875])).

tff(c_13883,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_7499,c_13881])).

tff(c_13886,plain,(
    ! [B_721] :
      ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_721)))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_721)))
      | k9_tmap_1('#skF_4',B_721) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_721,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_13124])).

tff(c_13910,plain,(
    ! [B_177] :
      ( ~ m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_177)))
      | k9_tmap_1('#skF_4',B_177) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_13886])).

tff(c_13928,plain,(
    ! [B_177] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_177)))
      | k9_tmap_1('#skF_4',B_177) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_177,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_56,c_58,c_7240,c_13910])).

tff(c_13930,plain,(
    ! [B_722] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_4',B_722)))
      | k9_tmap_1('#skF_4',B_722) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_722,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13928])).

tff(c_13954,plain,(
    ! [B_177] :
      ( ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')),u1_struct_0('#skF_4'),u1_struct_0('#skF_4'))
      | k9_tmap_1('#skF_4',B_177) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_177,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_13930])).

tff(c_13972,plain,(
    ! [B_177] :
      ( k9_tmap_1('#skF_4',B_177) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_177,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_56,c_58,c_4263,c_13954])).

tff(c_13974,plain,(
    ! [B_723] :
      ( k9_tmap_1('#skF_4',B_723) = k6_partfun1(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_723,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13972])).

tff(c_13983,plain,(
    k6_partfun1(u1_struct_0('#skF_4')) = k9_tmap_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_13974])).

tff(c_765,plain,(
    ! [C_188,A_189,D_190] :
      ( r1_tmap_1(C_188,k6_tmap_1(A_189,u1_struct_0(C_188)),k2_tmap_1(A_189,k6_tmap_1(A_189,u1_struct_0(C_188)),k7_tmap_1(A_189,u1_struct_0(C_188)),C_188),D_190)
      | ~ m1_subset_1(D_190,u1_struct_0(C_188))
      | ~ m1_pre_topc(C_188,A_189)
      | v2_struct_0(C_188)
      | ~ m1_subset_1(u1_struct_0(C_188),k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_804,plain,(
    ! [B_82,A_80,D_190] :
      ( r1_tmap_1(B_82,k6_tmap_1(A_80,u1_struct_0(B_82)),k2_tmap_1(A_80,k6_tmap_1(A_80,u1_struct_0(B_82)),k6_partfun1(u1_struct_0(A_80)),B_82),D_190)
      | ~ m1_subset_1(D_190,u1_struct_0(B_82))
      | ~ m1_pre_topc(B_82,A_80)
      | v2_struct_0(B_82)
      | ~ m1_subset_1(u1_struct_0(B_82),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80)
      | ~ m1_pre_topc(B_82,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_765])).

tff(c_14069,plain,(
    ! [B_82,D_190] :
      ( r1_tmap_1(B_82,k6_tmap_1('#skF_4',u1_struct_0(B_82)),k2_tmap_1('#skF_4',k6_tmap_1('#skF_4',u1_struct_0(B_82)),k9_tmap_1('#skF_4','#skF_5'),B_82),D_190)
      | ~ m1_subset_1(D_190,u1_struct_0(B_82))
      | ~ m1_pre_topc(B_82,'#skF_4')
      | v2_struct_0(B_82)
      | ~ m1_subset_1(u1_struct_0(B_82),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_82,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13983,c_804])).

tff(c_14127,plain,(
    ! [B_82,D_190] :
      ( r1_tmap_1(B_82,k6_tmap_1('#skF_4',u1_struct_0(B_82)),k2_tmap_1('#skF_4',k6_tmap_1('#skF_4',u1_struct_0(B_82)),k9_tmap_1('#skF_4','#skF_5'),B_82),D_190)
      | ~ m1_subset_1(D_190,u1_struct_0(B_82))
      | v2_struct_0(B_82)
      | ~ m1_subset_1(u1_struct_0(B_82),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_82,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_58,c_56,c_14069])).

tff(c_16659,plain,(
    ! [B_757,D_758] :
      ( r1_tmap_1(B_757,k6_tmap_1('#skF_4',u1_struct_0(B_757)),k2_tmap_1('#skF_4',k6_tmap_1('#skF_4',u1_struct_0(B_757)),k9_tmap_1('#skF_4','#skF_5'),B_757),D_758)
      | ~ m1_subset_1(D_758,u1_struct_0(B_757))
      | v2_struct_0(B_757)
      | ~ m1_subset_1(u1_struct_0(B_757),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_757,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_14127])).

tff(c_16735,plain,(
    ! [B_61,D_758] :
      ( r1_tmap_1(B_61,k8_tmap_1('#skF_4',B_61),k2_tmap_1('#skF_4',k6_tmap_1('#skF_4',u1_struct_0(B_61)),k9_tmap_1('#skF_4','#skF_5'),B_61),D_758)
      | ~ m1_subset_1(D_758,u1_struct_0(B_61))
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_16659])).

tff(c_16759,plain,(
    ! [B_61,D_758] :
      ( r1_tmap_1(B_61,k8_tmap_1('#skF_4',B_61),k2_tmap_1('#skF_4',k6_tmap_1('#skF_4',u1_struct_0(B_61)),k9_tmap_1('#skF_4','#skF_5'),B_61),D_758)
      | ~ m1_subset_1(D_758,u1_struct_0(B_61))
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_16735])).

tff(c_16764,plain,(
    ! [B_759,D_760] :
      ( r1_tmap_1(B_759,k8_tmap_1('#skF_4',B_759),k2_tmap_1('#skF_4',k6_tmap_1('#skF_4',u1_struct_0(B_759)),k9_tmap_1('#skF_4','#skF_5'),B_759),D_760)
      | ~ m1_subset_1(D_760,u1_struct_0(B_759))
      | v2_struct_0(B_759)
      | ~ m1_subset_1(u1_struct_0(B_759),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_759,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_16759])).

tff(c_16808,plain,(
    ! [B_61,D_760] :
      ( r1_tmap_1(B_61,k8_tmap_1('#skF_4',B_61),k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_61),k9_tmap_1('#skF_4','#skF_5'),B_61),D_760)
      | ~ m1_subset_1(D_760,u1_struct_0(B_61))
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ m1_pre_topc(B_61,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_16764])).

tff(c_16822,plain,(
    ! [B_61,D_760] :
      ( r1_tmap_1(B_61,k8_tmap_1('#skF_4',B_61),k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_61),k9_tmap_1('#skF_4','#skF_5'),B_61),D_760)
      | ~ m1_subset_1(D_760,u1_struct_0(B_61))
      | v2_struct_0(B_61)
      | ~ m1_subset_1(u1_struct_0(B_61),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_61,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_16808])).

tff(c_16824,plain,(
    ! [B_761,D_762] :
      ( r1_tmap_1(B_761,k8_tmap_1('#skF_4',B_761),k2_tmap_1('#skF_4',k8_tmap_1('#skF_4',B_761),k9_tmap_1('#skF_4','#skF_5'),B_761),D_762)
      | ~ m1_subset_1(D_762,u1_struct_0(B_761))
      | v2_struct_0(B_761)
      | ~ m1_subset_1(u1_struct_0(B_761),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_761,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_16822])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_5',k8_tmap_1('#skF_4','#skF_5'),k2_tmap_1('#skF_4',k8_tmap_1('#skF_4','#skF_5'),k9_tmap_1('#skF_4','#skF_5'),'#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_16827,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_16824,c_48])).

tff(c_16838,plain,
    ( v2_struct_0('#skF_5')
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_16827])).

tff(c_16839,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_16838])).

tff(c_16848,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_16839])).

tff(c_16852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_16848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.82/6.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.95/6.94  
% 16.95/6.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.95/6.94  %$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k5_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k6_partfun1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 16.95/6.94  
% 16.95/6.94  %Foreground sorts:
% 16.95/6.94  
% 16.95/6.94  
% 16.95/6.94  %Background operators:
% 16.95/6.94  
% 16.95/6.94  
% 16.95/6.94  %Foreground operators:
% 16.95/6.94  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.95/6.94  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 16.95/6.94  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 16.95/6.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.95/6.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.95/6.94  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.95/6.94  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 16.95/6.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.95/6.94  tff('#skF_5', type, '#skF_5': $i).
% 16.95/6.94  tff(k9_tmap_1, type, k9_tmap_1: ($i * $i) > $i).
% 16.95/6.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.95/6.94  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 16.95/6.94  tff('#skF_6', type, '#skF_6': $i).
% 16.95/6.94  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.95/6.94  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 16.95/6.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.95/6.94  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 16.95/6.94  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 16.95/6.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.95/6.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.95/6.94  tff('#skF_4', type, '#skF_4': $i).
% 16.95/6.94  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 16.95/6.94  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 16.95/6.94  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.95/6.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.95/6.94  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 16.95/6.94  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.95/6.94  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 16.95/6.94  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 16.95/6.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.95/6.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.95/6.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.95/6.94  
% 16.95/6.97  tff(f_219, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tmap_1(B, k8_tmap_1(A, B), k2_tmap_1(A, k8_tmap_1(A, B), k9_tmap_1(A, B), B), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_tmap_1)).
% 16.95/6.97  tff(f_200, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 16.95/6.97  tff(f_156, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 16.95/6.97  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 16.95/6.97  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 16.95/6.97  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k7_tmap_1(A, B) = k6_partfun1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_tmap_1)).
% 16.95/6.97  tff(f_141, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 16.95/6.97  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 16.95/6.97  tff(f_62, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 16.95/6.97  tff(f_42, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 16.95/6.97  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (?[B]: m1_pre_topc(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_pre_topc)).
% 16.95/6.97  tff(f_126, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)))))) => ((C = k9_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => r1_funct_2(u1_struct_0(A), u1_struct_0(k8_tmap_1(A, B)), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, D)), C, k7_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_tmap_1)).
% 16.95/6.97  tff(f_193, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => ((u1_struct_0(C) = B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_tmap_1)).
% 16.95/6.97  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.95/6.97  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.95/6.97  tff(c_46, plain, (![B_82, A_80]: (m1_subset_1(u1_struct_0(B_82), k1_zfmisc_1(u1_struct_0(A_80))) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_200])).
% 16.95/6.97  tff(c_54, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.95/6.97  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.95/6.97  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.95/6.97  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.95/6.97  tff(c_34, plain, (![A_60, B_61]: (l1_pre_topc(k8_tmap_1(A_60, B_61)) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_156])).
% 16.95/6.97  tff(c_38, plain, (![A_60, B_61]: (v1_pre_topc(k8_tmap_1(A_60, B_61)) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_156])).
% 16.95/6.97  tff(c_36, plain, (![A_60, B_61]: (v2_pre_topc(k8_tmap_1(A_60, B_61)) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_156])).
% 16.95/6.97  tff(c_302, plain, (![A_145, B_146]: (k6_tmap_1(A_145, u1_struct_0(B_146))=k8_tmap_1(A_145, B_146) | ~m1_subset_1(u1_struct_0(B_146), k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(k8_tmap_1(A_145, B_146)) | ~v2_pre_topc(k8_tmap_1(A_145, B_146)) | ~v1_pre_topc(k8_tmap_1(A_145, B_146)) | ~m1_pre_topc(B_146, A_145) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_100])).
% 16.95/6.97  tff(c_543, plain, (![A_167, B_168]: (k6_tmap_1(A_167, u1_struct_0(B_168))=k8_tmap_1(A_167, B_168) | ~l1_pre_topc(k8_tmap_1(A_167, B_168)) | ~v2_pre_topc(k8_tmap_1(A_167, B_168)) | ~v1_pre_topc(k8_tmap_1(A_167, B_168)) | ~v2_pre_topc(A_167) | v2_struct_0(A_167) | ~m1_pre_topc(B_168, A_167) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_46, c_302])).
% 16.95/6.97  tff(c_548, plain, (![A_169, B_170]: (k6_tmap_1(A_169, u1_struct_0(B_170))=k8_tmap_1(A_169, B_170) | ~l1_pre_topc(k8_tmap_1(A_169, B_170)) | ~v1_pre_topc(k8_tmap_1(A_169, B_170)) | ~m1_pre_topc(B_170, A_169) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_36, c_543])).
% 16.95/6.97  tff(c_553, plain, (![A_171, B_172]: (k6_tmap_1(A_171, u1_struct_0(B_172))=k8_tmap_1(A_171, B_172) | ~l1_pre_topc(k8_tmap_1(A_171, B_172)) | ~m1_pre_topc(B_172, A_171) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(resolution, [status(thm)], [c_38, c_548])).
% 16.95/6.97  tff(c_557, plain, (![A_60, B_61]: (k6_tmap_1(A_60, u1_struct_0(B_61))=k8_tmap_1(A_60, B_61) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_34, c_553])).
% 16.95/6.97  tff(c_73, plain, (![A_100, B_101]: (u1_struct_0(k6_tmap_1(A_100, B_101))=u1_struct_0(A_100) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_170])).
% 16.95/6.97  tff(c_77, plain, (![A_80, B_82]: (u1_struct_0(k6_tmap_1(A_80, u1_struct_0(B_82)))=u1_struct_0(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_46, c_73])).
% 16.95/6.97  tff(c_112, plain, (![A_106, B_107]: (k7_tmap_1(A_106, B_107)=k6_partfun1(u1_struct_0(A_106)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.95/6.97  tff(c_119, plain, (![A_80, B_82]: (k7_tmap_1(A_80, u1_struct_0(B_82))=k6_partfun1(u1_struct_0(A_80)) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_46, c_112])).
% 16.95/6.97  tff(c_155, plain, (![A_114, B_115]: (v1_funct_2(k7_tmap_1(A_114, B_115), u1_struct_0(A_114), u1_struct_0(k6_tmap_1(A_114, B_115))) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.95/6.97  tff(c_1074, plain, (![A_222, B_223]: (v1_funct_2(k6_partfun1(u1_struct_0(A_222)), u1_struct_0(A_222), u1_struct_0(k6_tmap_1(A_222, u1_struct_0(B_223)))) | ~m1_subset_1(u1_struct_0(B_223), k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222) | ~m1_pre_topc(B_223, A_222) | ~l1_pre_topc(A_222))), inference(superposition, [status(thm), theory('equality')], [c_119, c_155])).
% 16.95/6.97  tff(c_4188, plain, (![A_396, B_397]: (v1_funct_2(k6_partfun1(u1_struct_0(A_396)), u1_struct_0(A_396), u1_struct_0(A_396)) | ~m1_subset_1(u1_struct_0(B_397), k1_zfmisc_1(u1_struct_0(A_396))) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396) | ~m1_pre_topc(B_397, A_396) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396) | ~m1_pre_topc(B_397, A_396) | ~l1_pre_topc(A_396))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1074])).
% 16.95/6.97  tff(c_4254, plain, (![A_398, B_399]: (v1_funct_2(k6_partfun1(u1_struct_0(A_398)), u1_struct_0(A_398), u1_struct_0(A_398)) | ~v2_pre_topc(A_398) | v2_struct_0(A_398) | ~m1_pre_topc(B_399, A_398) | ~l1_pre_topc(A_398))), inference(resolution, [status(thm)], [c_46, c_4188])).
% 16.95/6.97  tff(c_4258, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_4254])).
% 16.95/6.97  tff(c_4262, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_4258])).
% 16.95/6.97  tff(c_4263, plain, (v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_4262])).
% 16.95/6.97  tff(c_568, plain, (![A_176, B_177]: (k6_tmap_1(A_176, u1_struct_0(B_177))=k8_tmap_1(A_176, B_177) | ~m1_pre_topc(B_177, A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_34, c_553])).
% 16.95/6.97  tff(c_609, plain, (![A_176, B_177]: (u1_struct_0(k8_tmap_1(A_176, B_177))=u1_struct_0(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176) | ~m1_pre_topc(B_177, A_176) | ~l1_pre_topc(A_176) | ~m1_pre_topc(B_177, A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(superposition, [status(thm), theory('equality')], [c_568, c_77])).
% 16.95/6.97  tff(c_179, plain, (![A_120, B_121]: (m1_subset_1(k7_tmap_1(A_120, B_121), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_120), u1_struct_0(k6_tmap_1(A_120, B_121))))) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.95/6.97  tff(c_1974, plain, (![A_277, B_278]: (m1_subset_1(k6_partfun1(u1_struct_0(A_277)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_277), u1_struct_0(k6_tmap_1(A_277, u1_struct_0(B_278)))))) | ~m1_subset_1(u1_struct_0(B_278), k1_zfmisc_1(u1_struct_0(A_277))) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277) | ~m1_pre_topc(B_278, A_277) | ~l1_pre_topc(A_277))), inference(superposition, [status(thm), theory('equality')], [c_119, c_179])).
% 16.95/6.97  tff(c_7150, plain, (![A_460, B_461]: (m1_subset_1(k6_partfun1(u1_struct_0(A_460)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_460), u1_struct_0(A_460)))) | ~m1_subset_1(u1_struct_0(B_461), k1_zfmisc_1(u1_struct_0(A_460))) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460) | ~m1_pre_topc(B_461, A_460) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460) | ~m1_pre_topc(B_461, A_460) | ~l1_pre_topc(A_460))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1974])).
% 16.95/6.97  tff(c_7231, plain, (![A_462, B_463]: (m1_subset_1(k6_partfun1(u1_struct_0(A_462)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_462), u1_struct_0(A_462)))) | ~v2_pre_topc(A_462) | v2_struct_0(A_462) | ~m1_pre_topc(B_463, A_462) | ~l1_pre_topc(A_462))), inference(resolution, [status(thm)], [c_46, c_7150])).
% 16.95/6.97  tff(c_7235, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4')))) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_7231])).
% 16.95/6.97  tff(c_7239, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4')))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_7235])).
% 16.95/6.97  tff(c_7240, plain, (m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_7239])).
% 16.95/6.97  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.95/6.97  tff(c_128, plain, (![A_110, B_111]: (k7_tmap_1(A_110, u1_struct_0(B_111))=k6_partfun1(u1_struct_0(A_110)) | ~v2_pre_topc(A_110) | v2_struct_0(A_110) | ~m1_pre_topc(B_111, A_110) | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_46, c_112])).
% 16.95/6.97  tff(c_68, plain, (![A_98, B_99]: (v1_funct_1(k7_tmap_1(A_98, B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_141])).
% 16.95/6.97  tff(c_72, plain, (![A_80, B_82]: (v1_funct_1(k7_tmap_1(A_80, u1_struct_0(B_82))) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(resolution, [status(thm)], [c_46, c_68])).
% 16.95/6.97  tff(c_169, plain, (![A_118, B_119]: (v1_funct_1(k6_partfun1(u1_struct_0(A_118))) | ~v2_pre_topc(A_118) | v2_struct_0(A_118) | ~m1_pre_topc(B_119, A_118) | ~l1_pre_topc(A_118) | ~v2_pre_topc(A_118) | v2_struct_0(A_118) | ~m1_pre_topc(B_119, A_118) | ~l1_pre_topc(A_118))), inference(superposition, [status(thm), theory('equality')], [c_128, c_72])).
% 16.95/6.97  tff(c_173, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_4'))) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_169])).
% 16.95/6.97  tff(c_177, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_58, c_173])).
% 16.95/6.97  tff(c_178, plain, (v1_funct_1(k6_partfun1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_177])).
% 16.95/6.97  tff(c_8, plain, (![B_6, C_7, E_9, D_8, A_5, F_10]: (r1_funct_2(A_5, B_6, C_7, D_8, E_9, E_9) | ~m1_subset_1(F_10, k1_zfmisc_1(k2_zfmisc_1(C_7, D_8))) | ~v1_funct_2(F_10, C_7, D_8) | ~v1_funct_1(F_10) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(E_9, A_5, B_6) | ~v1_funct_1(E_9) | v1_xboole_0(D_8) | v1_xboole_0(B_6))), inference(cnfTransformation, [status(thm)], [f_62])).
% 16.95/6.97  tff(c_7242, plain, (![A_5, B_6, E_9]: (r1_funct_2(A_5, B_6, u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), E_9, E_9) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_4')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_4'))) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(E_9, A_5, B_6) | ~v1_funct_1(E_9) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_6))), inference(resolution, [status(thm)], [c_7240, c_8])).
% 16.95/6.97  tff(c_7245, plain, (![A_5, B_6, E_9]: (r1_funct_2(A_5, B_6, u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), E_9, E_9) | ~m1_subset_1(E_9, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))) | ~v1_funct_2(E_9, A_5, B_6) | ~v1_funct_1(E_9) | v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0(B_6))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_4263, c_7242])).
% 16.95/6.97  tff(c_7484, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_7245])).
% 16.95/6.97  tff(c_6, plain, (![A_4]: (~v1_xboole_0(u1_struct_0(A_4)) | ~l1_struct_0(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.95/6.97  tff(c_7487, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_7484, c_6])).
% 16.95/6.97  tff(c_7490, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_7487])).
% 16.95/6.97  tff(c_7493, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2, c_7490])).
% 16.95/6.97  tff(c_7497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_7493])).
% 16.95/6.97  tff(c_7499, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_7245])).
% 16.95/6.97  tff(c_4, plain, (![A_2]: (m1_pre_topc('#skF_1'(A_2), A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.95/6.97  tff(c_4259, plain, (![A_2]: (v1_funct_2(k6_partfun1(u1_struct_0(A_2)), u1_struct_0(A_2), u1_struct_0(A_2)) | ~v2_pre_topc(A_2) | v2_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(resolution, [status(thm)], [c_4, c_4254])).
% 16.95/6.97  tff(c_7246, plain, (![A_464]: (m1_subset_1(k6_partfun1(u1_struct_0(A_464)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_464), u1_struct_0(A_464)))) | ~v2_pre_topc(A_464) | v2_struct_0(A_464) | ~l1_pre_topc(A_464))), inference(resolution, [status(thm)], [c_4, c_7231])).
% 16.95/6.97  tff(c_13125, plain, (![A_700, B_701, A_702, E_703]: (r1_funct_2(A_700, B_701, u1_struct_0(A_702), u1_struct_0(A_702), E_703, E_703) | ~v1_funct_2(k6_partfun1(u1_struct_0(A_702)), u1_struct_0(A_702), u1_struct_0(A_702)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_702))) | ~m1_subset_1(E_703, k1_zfmisc_1(k2_zfmisc_1(A_700, B_701))) | ~v1_funct_2(E_703, A_700, B_701) | ~v1_funct_1(E_703) | v1_xboole_0(u1_struct_0(A_702)) | v1_xboole_0(B_701) | ~v2_pre_topc(A_702) | v2_struct_0(A_702) | ~l1_pre_topc(A_702))), inference(resolution, [status(thm)], [c_7246, c_8])).
% 16.95/6.97  tff(c_13214, plain, (![A_700, B_701, A_2, E_703]: (r1_funct_2(A_700, B_701, u1_struct_0(A_2), u1_struct_0(A_2), E_703, E_703) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_2))) | ~m1_subset_1(E_703, k1_zfmisc_1(k2_zfmisc_1(A_700, B_701))) | ~v1_funct_2(E_703, A_700, B_701) | ~v1_funct_1(E_703) | v1_xboole_0(u1_struct_0(A_2)) | v1_xboole_0(B_701) | ~v2_pre_topc(A_2) | v2_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(resolution, [status(thm)], [c_4259, c_13125])).
% 16.95/6.97  tff(c_189, plain, (![A_122]: (v1_funct_1(k6_partfun1(u1_struct_0(A_122))) | ~v2_pre_topc(A_122) | v2_struct_0(A_122) | ~m1_pre_topc('#skF_1'(A_122), A_122) | ~l1_pre_topc(A_122))), inference(resolution, [status(thm)], [c_4, c_169])).
% 16.95/6.97  tff(c_192, plain, (![A_2]: (v1_funct_1(k6_partfun1(u1_struct_0(A_2))) | ~v2_pre_topc(A_2) | v2_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(resolution, [status(thm)], [c_4, c_189])).
% 16.95/6.97  tff(c_1086, plain, (![A_60, B_61]: (v1_funct_2(k6_partfun1(u1_struct_0(A_60)), u1_struct_0(A_60), u1_struct_0(k8_tmap_1(A_60, B_61))) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~m1_pre_topc(B_61, A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_557, c_1074])).
% 16.95/6.97  tff(c_9168, plain, (![A_541, B_542]: (m1_subset_1(k6_partfun1(u1_struct_0(A_541)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_541), u1_struct_0(k8_tmap_1(A_541, B_542))))) | ~m1_subset_1(u1_struct_0(B_542), k1_zfmisc_1(u1_struct_0(A_541))) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541) | ~m1_pre_topc(B_542, A_541) | ~l1_pre_topc(A_541) | ~m1_pre_topc(B_542, A_541) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541))), inference(superposition, [status(thm), theory('equality')], [c_557, c_1974])).
% 16.95/6.97  tff(c_24, plain, (![B_48, A_36, C_54]: (u1_struct_0(B_48)='#skF_3'(A_36, B_48, C_54) | k9_tmap_1(A_36, B_48)=C_54 | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48))))) | ~v1_funct_2(C_54, u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48))) | ~v1_funct_1(C_54) | ~m1_pre_topc(B_48, A_36) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.95/6.97  tff(c_10479, plain, (![A_602, B_603]: ('#skF_3'(A_602, B_603, k6_partfun1(u1_struct_0(A_602)))=u1_struct_0(B_603) | k9_tmap_1(A_602, B_603)=k6_partfun1(u1_struct_0(A_602)) | ~v1_funct_2(k6_partfun1(u1_struct_0(A_602)), u1_struct_0(A_602), u1_struct_0(k8_tmap_1(A_602, B_603))) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_602))) | ~m1_subset_1(u1_struct_0(B_603), k1_zfmisc_1(u1_struct_0(A_602))) | ~m1_pre_topc(B_603, A_602) | ~l1_pre_topc(A_602) | ~v2_pre_topc(A_602) | v2_struct_0(A_602))), inference(resolution, [status(thm)], [c_9168, c_24])).
% 16.95/6.97  tff(c_10583, plain, (![A_604, B_605]: ('#skF_3'(A_604, B_605, k6_partfun1(u1_struct_0(A_604)))=u1_struct_0(B_605) | k9_tmap_1(A_604, B_605)=k6_partfun1(u1_struct_0(A_604)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_604))) | ~m1_subset_1(u1_struct_0(B_605), k1_zfmisc_1(u1_struct_0(A_604))) | ~m1_pre_topc(B_605, A_604) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(resolution, [status(thm)], [c_1086, c_10479])).
% 16.95/6.97  tff(c_10664, plain, (![A_606, B_607]: ('#skF_3'(A_606, B_607, k6_partfun1(u1_struct_0(A_606)))=u1_struct_0(B_607) | k9_tmap_1(A_606, B_607)=k6_partfun1(u1_struct_0(A_606)) | ~v1_funct_1(k6_partfun1(u1_struct_0(A_606))) | ~v2_pre_topc(A_606) | v2_struct_0(A_606) | ~m1_pre_topc(B_607, A_606) | ~l1_pre_topc(A_606))), inference(resolution, [status(thm)], [c_46, c_10583])).
% 16.95/6.97  tff(c_10697, plain, (![A_2, B_607]: ('#skF_3'(A_2, B_607, k6_partfun1(u1_struct_0(A_2)))=u1_struct_0(B_607) | k9_tmap_1(A_2, B_607)=k6_partfun1(u1_struct_0(A_2)) | ~m1_pre_topc(B_607, A_2) | ~v2_pre_topc(A_2) | v2_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(resolution, [status(thm)], [c_192, c_10664])).
% 16.95/6.97  tff(c_10694, plain, (![B_607]: ('#skF_3'('#skF_4', B_607, k6_partfun1(u1_struct_0('#skF_4')))=u1_struct_0(B_607) | k9_tmap_1('#skF_4', B_607)=k6_partfun1(u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_607, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_178, c_10664])).
% 16.95/6.97  tff(c_10700, plain, (![B_607]: ('#skF_3'('#skF_4', B_607, k6_partfun1(u1_struct_0('#skF_4')))=u1_struct_0(B_607) | k9_tmap_1('#skF_4', B_607)=k6_partfun1(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_607, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_10694])).
% 16.95/6.97  tff(c_10702, plain, (![B_608]: ('#skF_3'('#skF_4', B_608, k6_partfun1(u1_struct_0('#skF_4')))=u1_struct_0(B_608) | k9_tmap_1('#skF_4', B_608)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_608, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_10700])).
% 16.95/6.97  tff(c_22, plain, (![A_36, B_48, C_54]: (~r1_funct_2(u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48)), u1_struct_0(A_36), u1_struct_0(k6_tmap_1(A_36, '#skF_3'(A_36, B_48, C_54))), C_54, k7_tmap_1(A_36, '#skF_3'(A_36, B_48, C_54))) | k9_tmap_1(A_36, B_48)=C_54 | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48))))) | ~v1_funct_2(C_54, u1_struct_0(A_36), u1_struct_0(k8_tmap_1(A_36, B_48))) | ~v1_funct_1(C_54) | ~m1_pre_topc(B_48, A_36) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.95/6.97  tff(c_10708, plain, (![B_608]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_608)), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', u1_struct_0(B_608))), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', '#skF_3'('#skF_4', B_608, k6_partfun1(u1_struct_0('#skF_4'))))) | k9_tmap_1('#skF_4', B_608)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_608))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_608))) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_608, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | k9_tmap_1('#skF_4', B_608)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_608, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10702, c_22])).
% 16.95/6.97  tff(c_10717, plain, (![B_608]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_608)), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', u1_struct_0(B_608))), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', '#skF_3'('#skF_4', B_608, k6_partfun1(u1_struct_0('#skF_4'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_608))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_608))) | v2_struct_0('#skF_4') | k9_tmap_1('#skF_4', B_608)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_608, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_178, c_10708])).
% 16.95/6.97  tff(c_11006, plain, (![B_620]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_620)), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', u1_struct_0(B_620))), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', '#skF_3'('#skF_4', B_620, k6_partfun1(u1_struct_0('#skF_4'))))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_620))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_620))) | k9_tmap_1('#skF_4', B_620)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_620, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_10717])).
% 16.95/6.97  tff(c_11010, plain, (![B_607]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_607)), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', u1_struct_0(B_607))), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_607))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_607))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_607))) | k9_tmap_1('#skF_4', B_607)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_607, '#skF_4') | k9_tmap_1('#skF_4', B_607)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_607, '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10697, c_11006])).
% 16.95/6.97  tff(c_11113, plain, (![B_607]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_607)), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', u1_struct_0(B_607))), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_607))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_607))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_607))) | k9_tmap_1('#skF_4', B_607)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_607, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_11010])).
% 16.95/6.97  tff(c_11617, plain, (![B_647]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_647)), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', u1_struct_0(B_647))), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_647))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_647))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_647))) | k9_tmap_1('#skF_4', B_647)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_647, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_11113])).
% 16.95/6.97  tff(c_11786, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82)), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_82))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))) | k9_tmap_1('#skF_4', B_82)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_82, '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_82, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_11617])).
% 16.95/6.97  tff(c_11854, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82)), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_82))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))) | k9_tmap_1('#skF_4', B_82)=k6_partfun1(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_82, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_11786])).
% 16.95/6.97  tff(c_12445, plain, (![B_675]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_675)), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_675))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_675))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_675))) | k9_tmap_1('#skF_4', B_675)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_675, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_11854])).
% 16.95/6.97  tff(c_12519, plain, (![B_177]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_177))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_177))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_177))) | k9_tmap_1('#skF_4', B_177)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_177, '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_177, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_177, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_609, c_12445])).
% 16.95/6.97  tff(c_12571, plain, (![B_177]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_177))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_177))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_177))) | k9_tmap_1('#skF_4', B_177)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_177, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_56, c_58, c_12519])).
% 16.95/6.97  tff(c_13026, plain, (![B_699]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k7_tmap_1('#skF_4', u1_struct_0(B_699))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_699))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_699))) | k9_tmap_1('#skF_4', B_699)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_699, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_12571])).
% 16.95/6.97  tff(c_13097, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k6_partfun1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))) | k9_tmap_1('#skF_4', B_82)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_82, '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_82, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_119, c_13026])).
% 16.95/6.97  tff(c_13123, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k6_partfun1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))) | k9_tmap_1('#skF_4', B_82)=k6_partfun1(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_82, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_13097])).
% 16.95/6.97  tff(c_13124, plain, (![B_82]: (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k6_partfun1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_82))) | k9_tmap_1('#skF_4', B_82)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_82, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_13123])).
% 16.95/6.97  tff(c_13872, plain, (~r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_4'), k6_partfun1(u1_struct_0('#skF_4')), k6_partfun1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_13124])).
% 16.95/6.97  tff(c_13875, plain, (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_4')) | ~v1_funct_1(k6_partfun1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4')) | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_13214, c_13872])).
% 16.95/6.97  tff(c_13881, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_178, c_4263, c_7240, c_13875])).
% 16.95/6.97  tff(c_13883, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_7499, c_13881])).
% 16.95/6.97  tff(c_13886, plain, (![B_721]: (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_721))))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_721))) | k9_tmap_1('#skF_4', B_721)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_721, '#skF_4'))), inference(splitRight, [status(thm)], [c_13124])).
% 16.95/6.97  tff(c_13910, plain, (![B_177]: (~m1_subset_1(k6_partfun1(u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_177))) | k9_tmap_1('#skF_4', B_177)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_177, '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_177, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_177, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_609, c_13886])).
% 16.95/6.97  tff(c_13928, plain, (![B_177]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_177))) | k9_tmap_1('#skF_4', B_177)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_177, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_56, c_58, c_7240, c_13910])).
% 16.95/6.97  tff(c_13930, plain, (![B_722]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0(k8_tmap_1('#skF_4', B_722))) | k9_tmap_1('#skF_4', B_722)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_722, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_13928])).
% 16.95/6.97  tff(c_13954, plain, (![B_177]: (~v1_funct_2(k6_partfun1(u1_struct_0('#skF_4')), u1_struct_0('#skF_4'), u1_struct_0('#skF_4')) | k9_tmap_1('#skF_4', B_177)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_177, '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_177, '#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_177, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_609, c_13930])).
% 16.95/6.97  tff(c_13972, plain, (![B_177]: (k9_tmap_1('#skF_4', B_177)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_177, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_56, c_58, c_4263, c_13954])).
% 16.95/6.97  tff(c_13974, plain, (![B_723]: (k9_tmap_1('#skF_4', B_723)=k6_partfun1(u1_struct_0('#skF_4')) | ~m1_pre_topc(B_723, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_13972])).
% 16.95/6.97  tff(c_13983, plain, (k6_partfun1(u1_struct_0('#skF_4'))=k9_tmap_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_13974])).
% 16.95/6.97  tff(c_765, plain, (![C_188, A_189, D_190]: (r1_tmap_1(C_188, k6_tmap_1(A_189, u1_struct_0(C_188)), k2_tmap_1(A_189, k6_tmap_1(A_189, u1_struct_0(C_188)), k7_tmap_1(A_189, u1_struct_0(C_188)), C_188), D_190) | ~m1_subset_1(D_190, u1_struct_0(C_188)) | ~m1_pre_topc(C_188, A_189) | v2_struct_0(C_188) | ~m1_subset_1(u1_struct_0(C_188), k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_193])).
% 16.95/6.97  tff(c_804, plain, (![B_82, A_80, D_190]: (r1_tmap_1(B_82, k6_tmap_1(A_80, u1_struct_0(B_82)), k2_tmap_1(A_80, k6_tmap_1(A_80, u1_struct_0(B_82)), k6_partfun1(u1_struct_0(A_80)), B_82), D_190) | ~m1_subset_1(D_190, u1_struct_0(B_82)) | ~m1_pre_topc(B_82, A_80) | v2_struct_0(B_82) | ~m1_subset_1(u1_struct_0(B_82), k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80) | ~m1_pre_topc(B_82, A_80) | ~l1_pre_topc(A_80))), inference(superposition, [status(thm), theory('equality')], [c_119, c_765])).
% 16.95/6.97  tff(c_14069, plain, (![B_82, D_190]: (r1_tmap_1(B_82, k6_tmap_1('#skF_4', u1_struct_0(B_82)), k2_tmap_1('#skF_4', k6_tmap_1('#skF_4', u1_struct_0(B_82)), k9_tmap_1('#skF_4', '#skF_5'), B_82), D_190) | ~m1_subset_1(D_190, u1_struct_0(B_82)) | ~m1_pre_topc(B_82, '#skF_4') | v2_struct_0(B_82) | ~m1_subset_1(u1_struct_0(B_82), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_82, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13983, c_804])).
% 16.95/6.97  tff(c_14127, plain, (![B_82, D_190]: (r1_tmap_1(B_82, k6_tmap_1('#skF_4', u1_struct_0(B_82)), k2_tmap_1('#skF_4', k6_tmap_1('#skF_4', u1_struct_0(B_82)), k9_tmap_1('#skF_4', '#skF_5'), B_82), D_190) | ~m1_subset_1(D_190, u1_struct_0(B_82)) | v2_struct_0(B_82) | ~m1_subset_1(u1_struct_0(B_82), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_82, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_58, c_56, c_14069])).
% 16.95/6.97  tff(c_16659, plain, (![B_757, D_758]: (r1_tmap_1(B_757, k6_tmap_1('#skF_4', u1_struct_0(B_757)), k2_tmap_1('#skF_4', k6_tmap_1('#skF_4', u1_struct_0(B_757)), k9_tmap_1('#skF_4', '#skF_5'), B_757), D_758) | ~m1_subset_1(D_758, u1_struct_0(B_757)) | v2_struct_0(B_757) | ~m1_subset_1(u1_struct_0(B_757), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_757, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_14127])).
% 16.95/6.97  tff(c_16735, plain, (![B_61, D_758]: (r1_tmap_1(B_61, k8_tmap_1('#skF_4', B_61), k2_tmap_1('#skF_4', k6_tmap_1('#skF_4', u1_struct_0(B_61)), k9_tmap_1('#skF_4', '#skF_5'), B_61), D_758) | ~m1_subset_1(D_758, u1_struct_0(B_61)) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_61, '#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_557, c_16659])).
% 16.95/6.97  tff(c_16759, plain, (![B_61, D_758]: (r1_tmap_1(B_61, k8_tmap_1('#skF_4', B_61), k2_tmap_1('#skF_4', k6_tmap_1('#skF_4', u1_struct_0(B_61)), k9_tmap_1('#skF_4', '#skF_5'), B_61), D_758) | ~m1_subset_1(D_758, u1_struct_0(B_61)) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_61, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_16735])).
% 16.95/6.97  tff(c_16764, plain, (![B_759, D_760]: (r1_tmap_1(B_759, k8_tmap_1('#skF_4', B_759), k2_tmap_1('#skF_4', k6_tmap_1('#skF_4', u1_struct_0(B_759)), k9_tmap_1('#skF_4', '#skF_5'), B_759), D_760) | ~m1_subset_1(D_760, u1_struct_0(B_759)) | v2_struct_0(B_759) | ~m1_subset_1(u1_struct_0(B_759), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_759, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_16759])).
% 16.95/6.97  tff(c_16808, plain, (![B_61, D_760]: (r1_tmap_1(B_61, k8_tmap_1('#skF_4', B_61), k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_61), k9_tmap_1('#skF_4', '#skF_5'), B_61), D_760) | ~m1_subset_1(D_760, u1_struct_0(B_61)) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_61, '#skF_4') | ~m1_pre_topc(B_61, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_557, c_16764])).
% 16.95/6.97  tff(c_16822, plain, (![B_61, D_760]: (r1_tmap_1(B_61, k8_tmap_1('#skF_4', B_61), k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_61), k9_tmap_1('#skF_4', '#skF_5'), B_61), D_760) | ~m1_subset_1(D_760, u1_struct_0(B_61)) | v2_struct_0(B_61) | ~m1_subset_1(u1_struct_0(B_61), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_61, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_16808])).
% 16.95/6.97  tff(c_16824, plain, (![B_761, D_762]: (r1_tmap_1(B_761, k8_tmap_1('#skF_4', B_761), k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', B_761), k9_tmap_1('#skF_4', '#skF_5'), B_761), D_762) | ~m1_subset_1(D_762, u1_struct_0(B_761)) | v2_struct_0(B_761) | ~m1_subset_1(u1_struct_0(B_761), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(B_761, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_16822])).
% 16.95/6.97  tff(c_48, plain, (~r1_tmap_1('#skF_5', k8_tmap_1('#skF_4', '#skF_5'), k2_tmap_1('#skF_4', k8_tmap_1('#skF_4', '#skF_5'), k9_tmap_1('#skF_4', '#skF_5'), '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 16.95/6.97  tff(c_16827, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_16824, c_48])).
% 16.95/6.97  tff(c_16838, plain, (v2_struct_0('#skF_5') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_16827])).
% 16.95/6.97  tff(c_16839, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_16838])).
% 16.95/6.97  tff(c_16848, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46, c_16839])).
% 16.95/6.97  tff(c_16852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_16848])).
% 16.95/6.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.95/6.97  
% 16.95/6.97  Inference rules
% 16.95/6.97  ----------------------
% 16.95/6.97  #Ref     : 0
% 16.95/6.97  #Sup     : 5096
% 16.95/6.97  #Fact    : 0
% 16.95/6.97  #Define  : 0
% 16.95/6.97  #Split   : 3
% 16.95/6.97  #Chain   : 0
% 16.95/6.97  #Close   : 0
% 16.95/6.97  
% 16.95/6.97  Ordering : KBO
% 16.95/6.97  
% 16.95/6.97  Simplification rules
% 16.95/6.97  ----------------------
% 16.95/6.97  #Subsume      : 350
% 16.95/6.97  #Demod        : 870
% 16.95/6.97  #Tautology    : 327
% 16.95/6.97  #SimpNegUnit  : 276
% 16.95/6.97  #BackRed      : 5
% 16.95/6.97  
% 16.95/6.97  #Partial instantiations: 0
% 16.95/6.97  #Strategies tried      : 1
% 16.95/6.97  
% 16.95/6.97  Timing (in seconds)
% 16.95/6.97  ----------------------
% 16.95/6.98  Preprocessing        : 0.38
% 16.95/6.98  Parsing              : 0.20
% 16.95/6.98  CNF conversion       : 0.03
% 16.95/6.98  Main loop            : 5.82
% 16.95/6.98  Inferencing          : 1.32
% 16.95/6.98  Reduction            : 1.21
% 16.95/6.98  Demodulation         : 0.83
% 16.95/6.98  BG Simplification    : 0.23
% 16.95/6.98  Subsumption          : 2.79
% 16.95/6.98  Abstraction          : 0.24
% 16.95/6.98  MUC search           : 0.00
% 16.95/6.98  Cooper               : 0.00
% 16.95/6.98  Total                : 6.25
% 16.95/6.98  Index Insertion      : 0.00
% 16.95/6.98  Index Deletion       : 0.00
% 16.95/6.98  Index Matching       : 0.00
% 16.95/6.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
