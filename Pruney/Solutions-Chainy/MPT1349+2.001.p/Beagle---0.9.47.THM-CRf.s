%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:50 EST 2020

% Result     : Theorem 50.88s
% Output     : CNFRefutation 51.13s
% Verified   : 
% Statistics : Number of formulae       :  204 (1696 expanded)
%              Number of leaves         :   45 ( 660 expanded)
%              Depth                    :   16
%              Number of atoms          :  737 (10577 expanded)
%              Number of equality atoms :   75 (1738 expanded)
%              Maximal formula depth    :   34 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v3_tops_2,type,(
    v3_tops_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_248,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_tops_2(C,A,B)
                <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(A,D)) = k2_pre_topc(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_2)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & v5_pre_topc(C,A,B)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_35,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_164,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                      & v2_funct_1(C) )
                   => k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k8_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

tff(f_143,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => r1_tarski(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(A,D)),k2_pre_topc(B,k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_183,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
               => v3_tops_2(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C),B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

tff(f_215,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_tops_2(C,A,B)
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(B,D)) = k2_pre_topc(A,k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_2)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_72,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_20,plain,(
    ! [A_31] :
      ( l1_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_106,plain,
    ( v3_tops_2('#skF_6','#skF_4','#skF_5')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_127,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_100,plain,
    ( v3_tops_2('#skF_6','#skF_4','#skF_5')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_122,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_94,plain,
    ( v3_tops_2('#skF_6','#skF_4','#skF_5')
    | v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_114,plain,(
    v2_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_86,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_135,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_122,c_114,c_86])).

tff(c_136,plain,(
    ~ v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_287,plain,(
    ! [A_166,B_167,C_168] :
      ( v4_pre_topc('#skF_1'(A_166,B_167,C_168),B_167)
      | v5_pre_topc(C_168,A_166,B_167)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0(A_166),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_pre_topc(B_167)
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_295,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_287])).

tff(c_300,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_68,c_295])).

tff(c_301,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_157,plain,(
    ! [A_144,B_145,C_146] :
      ( v1_funct_1(k2_tops_2(A_144,B_145,C_146))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2(C_146,A_144,B_145)
      | ~ v1_funct_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_164,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_157])).

tff(c_168,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_164])).

tff(c_169,plain,(
    ! [A_147,B_148,C_149] :
      ( v1_funct_2(k2_tops_2(A_147,B_148,C_149),B_148,A_147)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148)))
      | ~ v1_funct_2(C_149,A_147,B_148)
      | ~ v1_funct_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_174,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_169])).

tff(c_178,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_174])).

tff(c_38,plain,(
    ! [A_42,B_43,C_44] :
      ( m1_subset_1(k2_tops_2(A_42,B_43,C_44),k1_zfmisc_1(k2_zfmisc_1(B_43,A_42)))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(C_44,A_42,B_43)
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1405,plain,(
    ! [A_299,B_300,C_301] :
      ( v4_pre_topc('#skF_1'(A_299,B_300,k2_tops_2(u1_struct_0(B_300),u1_struct_0(A_299),C_301)),B_300)
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_300),u1_struct_0(A_299),C_301),A_299,B_300)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_300),u1_struct_0(A_299),C_301),u1_struct_0(A_299),u1_struct_0(B_300))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_300),u1_struct_0(A_299),C_301))
      | ~ l1_pre_topc(B_300)
      | ~ l1_pre_topc(A_299)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_300),u1_struct_0(A_299))))
      | ~ v1_funct_2(C_301,u1_struct_0(B_300),u1_struct_0(A_299))
      | ~ v1_funct_1(C_301) ) ),
    inference(resolution,[status(thm)],[c_38,c_287])).

tff(c_1413,plain,
    ( v4_pre_topc('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),'#skF_4')
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_178,c_1405])).

tff(c_1418,plain,
    ( v4_pre_topc('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),'#skF_4')
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_72,c_78,c_168,c_1413])).

tff(c_1419,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1418])).

tff(c_26,plain,(
    ! [C_41,A_35,B_39] :
      ( v3_tops_2(C_41,A_35,B_39)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_35),u1_struct_0(B_39),C_41),B_39,A_35)
      | ~ v5_pre_topc(C_41,A_35,B_39)
      | ~ v2_funct_1(C_41)
      | k2_relset_1(u1_struct_0(A_35),u1_struct_0(B_39),C_41) != k2_struct_0(B_39)
      | k1_relset_1(u1_struct_0(A_35),u1_struct_0(B_39),C_41) != k2_struct_0(A_35)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35),u1_struct_0(B_39))))
      | ~ v1_funct_2(C_41,u1_struct_0(A_35),u1_struct_0(B_39))
      | ~ v1_funct_1(C_41)
      | ~ l1_pre_topc(B_39)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1421,plain,
    ( v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1419,c_26])).

tff(c_1424,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_68,c_66,c_127,c_122,c_114,c_301,c_1421])).

tff(c_1426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_1424])).

tff(c_1428,plain,(
    ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1418])).

tff(c_313,plain,(
    ! [A_175,B_176,C_177] :
      ( m1_subset_1('#skF_1'(A_175,B_176,C_177),k1_zfmisc_1(u1_struct_0(B_176)))
      | v5_pre_topc(C_177,A_175,B_176)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175),u1_struct_0(B_176))))
      | ~ v1_funct_2(C_177,u1_struct_0(A_175),u1_struct_0(B_176))
      | ~ v1_funct_1(C_177)
      | ~ l1_pre_topc(B_176)
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_322,plain,(
    ! [A_175,B_176,C_44] :
      ( m1_subset_1('#skF_1'(A_175,B_176,k2_tops_2(u1_struct_0(B_176),u1_struct_0(A_175),C_44)),k1_zfmisc_1(u1_struct_0(B_176)))
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_176),u1_struct_0(A_175),C_44),A_175,B_176)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_176),u1_struct_0(A_175),C_44),u1_struct_0(A_175),u1_struct_0(B_176))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_176),u1_struct_0(A_175),C_44))
      | ~ l1_pre_topc(B_176)
      | ~ l1_pre_topc(A_175)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_176),u1_struct_0(A_175))))
      | ~ v1_funct_2(C_44,u1_struct_0(B_176),u1_struct_0(A_175))
      | ~ v1_funct_1(C_44) ) ),
    inference(resolution,[status(thm)],[c_38,c_313])).

tff(c_74,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( m1_subset_1(k7_relset_1(A_3,B_4,C_5,D_6),k1_zfmisc_1(B_4))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [B_142,A_143] :
      ( v4_pre_topc(B_142,A_143)
      | k2_pre_topc(A_143,B_142) != B_142
      | ~ v2_pre_topc(A_143)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_388,plain,(
    ! [A_190,A_191,C_192,D_193] :
      ( v4_pre_topc(k7_relset_1(A_190,u1_struct_0(A_191),C_192,D_193),A_191)
      | k2_pre_topc(A_191,k7_relset_1(A_190,u1_struct_0(A_191),C_192,D_193)) != k7_relset_1(A_190,u1_struct_0(A_191),C_192,D_193)
      | ~ v2_pre_topc(A_191)
      | ~ l1_pre_topc(A_191)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,u1_struct_0(A_191)))) ) ),
    inference(resolution,[status(thm)],[c_8,c_147])).

tff(c_396,plain,(
    ! [D_193] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_193),'#skF_5')
      | k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_193)) != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_193)
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_388])).

tff(c_401,plain,(
    ! [D_193] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_193),'#skF_5')
      | k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_193)) != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_396])).

tff(c_726,plain,(
    ! [B_242,A_243,C_244,D_245] :
      ( k8_relset_1(u1_struct_0(B_242),u1_struct_0(A_243),k2_tops_2(u1_struct_0(A_243),u1_struct_0(B_242),C_244),D_245) = k7_relset_1(u1_struct_0(A_243),u1_struct_0(B_242),C_244,D_245)
      | ~ v2_funct_1(C_244)
      | k2_relset_1(u1_struct_0(A_243),u1_struct_0(B_242),C_244) != k2_struct_0(B_242)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(u1_struct_0(A_243)))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243),u1_struct_0(B_242))))
      | ~ v1_funct_2(C_244,u1_struct_0(A_243),u1_struct_0(B_242))
      | ~ v1_funct_1(C_244)
      | ~ l1_struct_0(B_242)
      | ~ l1_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_12,plain,(
    ! [A_7,B_19,C_25] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_7),u1_struct_0(B_19),C_25,'#skF_1'(A_7,B_19,C_25)),A_7)
      | v5_pre_topc(C_25,A_7,B_19)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7),u1_struct_0(B_19))))
      | ~ v1_funct_2(C_25,u1_struct_0(A_7),u1_struct_0(B_19))
      | ~ v1_funct_1(C_25)
      | ~ l1_pre_topc(B_19)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_9325,plain,(
    ! [A_495,B_496,C_497] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_495),u1_struct_0(B_496),C_497,'#skF_1'(B_496,A_495,k2_tops_2(u1_struct_0(A_495),u1_struct_0(B_496),C_497))),B_496)
      | v5_pre_topc(k2_tops_2(u1_struct_0(A_495),u1_struct_0(B_496),C_497),B_496,A_495)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_495),u1_struct_0(B_496),C_497),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_496),u1_struct_0(A_495))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_495),u1_struct_0(B_496),C_497),u1_struct_0(B_496),u1_struct_0(A_495))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_495),u1_struct_0(B_496),C_497))
      | ~ l1_pre_topc(A_495)
      | ~ l1_pre_topc(B_496)
      | ~ v2_funct_1(C_497)
      | k2_relset_1(u1_struct_0(A_495),u1_struct_0(B_496),C_497) != k2_struct_0(B_496)
      | ~ m1_subset_1('#skF_1'(B_496,A_495,k2_tops_2(u1_struct_0(A_495),u1_struct_0(B_496),C_497)),k1_zfmisc_1(u1_struct_0(A_495)))
      | ~ m1_subset_1(C_497,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_495),u1_struct_0(B_496))))
      | ~ v1_funct_2(C_497,u1_struct_0(A_495),u1_struct_0(B_496))
      | ~ v1_funct_1(C_497)
      | ~ l1_struct_0(B_496)
      | ~ l1_struct_0(A_495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_12])).

tff(c_9337,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))) != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(resolution,[status(thm)],[c_401,c_9325])).

tff(c_9342,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))) != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_122,c_114,c_72,c_78,c_168,c_178,c_9337])).

tff(c_9343,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))) != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1428,c_9342])).

tff(c_9344,plain,(
    k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))) != k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_9343])).

tff(c_1427,plain,(
    v4_pre_topc('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1418])).

tff(c_1497,plain,(
    ! [A_315,B_316,C_317] :
      ( m1_subset_1('#skF_1'(A_315,B_316,k2_tops_2(u1_struct_0(B_316),u1_struct_0(A_315),C_317)),k1_zfmisc_1(u1_struct_0(B_316)))
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_316),u1_struct_0(A_315),C_317),A_315,B_316)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_316),u1_struct_0(A_315),C_317),u1_struct_0(A_315),u1_struct_0(B_316))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_316),u1_struct_0(A_315),C_317))
      | ~ l1_pre_topc(B_316)
      | ~ l1_pre_topc(A_315)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_316),u1_struct_0(A_315))))
      | ~ v1_funct_2(C_317,u1_struct_0(B_316),u1_struct_0(A_315))
      | ~ v1_funct_1(C_317) ) ),
    inference(resolution,[status(thm)],[c_38,c_313])).

tff(c_24,plain,(
    ! [A_32,B_34] :
      ( k2_pre_topc(A_32,B_34) = B_34
      | ~ v4_pre_topc(B_34,A_32)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12074,plain,(
    ! [B_525,A_526,C_527] :
      ( k2_pre_topc(B_525,'#skF_1'(A_526,B_525,k2_tops_2(u1_struct_0(B_525),u1_struct_0(A_526),C_527))) = '#skF_1'(A_526,B_525,k2_tops_2(u1_struct_0(B_525),u1_struct_0(A_526),C_527))
      | ~ v4_pre_topc('#skF_1'(A_526,B_525,k2_tops_2(u1_struct_0(B_525),u1_struct_0(A_526),C_527)),B_525)
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_525),u1_struct_0(A_526),C_527),A_526,B_525)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_525),u1_struct_0(A_526),C_527),u1_struct_0(A_526),u1_struct_0(B_525))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_525),u1_struct_0(A_526),C_527))
      | ~ l1_pre_topc(B_525)
      | ~ l1_pre_topc(A_526)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_525),u1_struct_0(A_526))))
      | ~ v1_funct_2(C_527,u1_struct_0(B_525),u1_struct_0(A_526))
      | ~ v1_funct_1(C_527) ) ),
    inference(resolution,[status(thm)],[c_1497,c_24])).

tff(c_12076,plain,
    ( k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))) = '#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1427,c_12074])).

tff(c_12079,plain,
    ( k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))) = '#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_72,c_78,c_168,c_178,c_12076])).

tff(c_12080,plain,(
    k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))) = '#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1428,c_12079])).

tff(c_88,plain,(
    ! [D_129] :
      ( v3_tops_2('#skF_6','#skF_4','#skF_5')
      | k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',D_129)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_129))
      | ~ m1_subset_1(D_129,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_188,plain,(
    ! [D_129] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',D_129)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_129))
      | ~ m1_subset_1(D_129,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_88])).

tff(c_12339,plain,
    ( k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))) = k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12080,c_188])).

tff(c_12441,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_9344,c_12339])).

tff(c_12449,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_322,c_12441])).

tff(c_12452,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_72,c_78,c_168,c_178,c_12449])).

tff(c_12454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1428,c_12452])).

tff(c_12455,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_9343])).

tff(c_12457,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_12455])).

tff(c_12473,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_12457])).

tff(c_12477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_12473])).

tff(c_12479,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_12455])).

tff(c_16,plain,(
    ! [A_7,B_19,C_25] :
      ( m1_subset_1('#skF_1'(A_7,B_19,C_25),k1_zfmisc_1(u1_struct_0(B_19)))
      | v5_pre_topc(C_25,A_7,B_19)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7),u1_struct_0(B_19))))
      | ~ v1_funct_2(C_25,u1_struct_0(A_7),u1_struct_0(B_19))
      | ~ v1_funct_1(C_25)
      | ~ l1_pre_topc(B_19)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12503,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12479,c_16])).

tff(c_12552,plain,
    ( m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_78,c_168,c_178,c_12503])).

tff(c_12553,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1428,c_12552])).

tff(c_12478,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12455])).

tff(c_12618,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12553,c_12478])).

tff(c_12619,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12618])).

tff(c_12634,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_12619])).

tff(c_12638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_12634])).

tff(c_12639,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_12618])).

tff(c_12643,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_12639])).

tff(c_12647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12643])).

tff(c_12649,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_80,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_12869,plain,(
    ! [A_578,B_579,C_580] :
      ( m1_subset_1('#skF_2'(A_578,B_579,C_580),k1_zfmisc_1(u1_struct_0(A_578)))
      | v5_pre_topc(C_580,A_578,B_579)
      | ~ m1_subset_1(C_580,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_578),u1_struct_0(B_579))))
      | ~ v1_funct_2(C_580,u1_struct_0(A_578),u1_struct_0(B_579))
      | ~ v1_funct_1(C_580)
      | ~ l1_pre_topc(B_579)
      | ~ v2_pre_topc(B_579)
      | v2_struct_0(B_579)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_12877,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_12869])).

tff(c_12882,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_70,c_68,c_12877])).

tff(c_12883,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_12649,c_12882])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13292,plain,(
    ! [A_632,B_633,C_634] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_632),u1_struct_0(B_633),C_634,k2_pre_topc(A_632,'#skF_2'(A_632,B_633,C_634))),k2_pre_topc(B_633,k7_relset_1(u1_struct_0(A_632),u1_struct_0(B_633),C_634,'#skF_2'(A_632,B_633,C_634))))
      | v5_pre_topc(C_634,A_632,B_633)
      | ~ m1_subset_1(C_634,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_632),u1_struct_0(B_633))))
      | ~ v1_funct_2(C_634,u1_struct_0(A_632),u1_struct_0(B_633))
      | ~ v1_funct_1(C_634)
      | ~ l1_pre_topc(B_633)
      | ~ v2_pre_topc(B_633)
      | v2_struct_0(B_633)
      | ~ l1_pre_topc(A_632)
      | ~ v2_pre_topc(A_632) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_13300,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_2'('#skF_4','#skF_5','#skF_6'))),k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_2'('#skF_4','#skF_5','#skF_6'))))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_13292])).

tff(c_13303,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12883,c_80,c_78,c_74,c_72,c_70,c_68,c_66,c_6,c_13300])).

tff(c_13305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_12649,c_13303])).

tff(c_13306,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_18,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_pre_topc(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_13343,plain,(
    ! [A_639,B_640,C_641] :
      ( v1_funct_1(k2_tops_2(A_639,B_640,C_641))
      | ~ m1_subset_1(C_641,k1_zfmisc_1(k2_zfmisc_1(A_639,B_640)))
      | ~ v1_funct_2(C_641,A_639,B_640)
      | ~ v1_funct_1(C_641) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_13350,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_13343])).

tff(c_13354,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_13350])).

tff(c_13307,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_13506,plain,(
    ! [A_679,B_680,C_681] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_679),u1_struct_0(B_680),C_681),B_680,A_679)
      | ~ v3_tops_2(C_681,A_679,B_680)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_679),u1_struct_0(B_680))))
      | ~ v1_funct_2(C_681,u1_struct_0(A_679),u1_struct_0(B_680))
      | ~ v1_funct_1(C_681)
      | ~ l1_pre_topc(B_680)
      | ~ l1_pre_topc(A_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_13514,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_13506])).

tff(c_13519,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_68,c_13307,c_13514])).

tff(c_13355,plain,(
    ! [A_642,B_643,C_644] :
      ( v1_funct_2(k2_tops_2(A_642,B_643,C_644),B_643,A_642)
      | ~ m1_subset_1(C_644,k1_zfmisc_1(k2_zfmisc_1(A_642,B_643)))
      | ~ v1_funct_2(C_644,A_642,B_643)
      | ~ v1_funct_1(C_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_13360,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_13355])).

tff(c_13364,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_13360])).

tff(c_50,plain,(
    ! [B_75,A_67,C_79,D_81] :
      ( k8_relset_1(u1_struct_0(B_75),u1_struct_0(A_67),k2_tops_2(u1_struct_0(A_67),u1_struct_0(B_75),C_79),D_81) = k7_relset_1(u1_struct_0(A_67),u1_struct_0(B_75),C_79,D_81)
      | ~ v2_funct_1(C_79)
      | k2_relset_1(u1_struct_0(A_67),u1_struct_0(B_75),C_79) != k2_struct_0(B_75)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_67),u1_struct_0(B_75))))
      | ~ v1_funct_2(C_79,u1_struct_0(A_67),u1_struct_0(B_75))
      | ~ v1_funct_1(C_79)
      | ~ l1_struct_0(B_75)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_13588,plain,(
    ! [A_713,B_714,C_715,D_716] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_713),u1_struct_0(B_714),C_715,D_716),A_713)
      | ~ v4_pre_topc(D_716,B_714)
      | ~ m1_subset_1(D_716,k1_zfmisc_1(u1_struct_0(B_714)))
      | ~ v5_pre_topc(C_715,A_713,B_714)
      | ~ m1_subset_1(C_715,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_713),u1_struct_0(B_714))))
      | ~ v1_funct_2(C_715,u1_struct_0(A_713),u1_struct_0(B_714))
      | ~ v1_funct_1(C_715)
      | ~ l1_pre_topc(B_714)
      | ~ l1_pre_topc(A_713) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_13827,plain,(
    ! [A_834,B_835,C_836,D_837] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_834),u1_struct_0(B_835),k2_tops_2(u1_struct_0(B_835),u1_struct_0(A_834),C_836),D_837),A_834)
      | ~ v4_pre_topc(D_837,B_835)
      | ~ m1_subset_1(D_837,k1_zfmisc_1(u1_struct_0(B_835)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(B_835),u1_struct_0(A_834),C_836),A_834,B_835)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_835),u1_struct_0(A_834),C_836),u1_struct_0(A_834),u1_struct_0(B_835))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_835),u1_struct_0(A_834),C_836))
      | ~ l1_pre_topc(B_835)
      | ~ l1_pre_topc(A_834)
      | ~ m1_subset_1(C_836,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_835),u1_struct_0(A_834))))
      | ~ v1_funct_2(C_836,u1_struct_0(B_835),u1_struct_0(A_834))
      | ~ v1_funct_1(C_836) ) ),
    inference(resolution,[status(thm)],[c_38,c_13588])).

tff(c_14107,plain,(
    ! [A_934,B_935,C_936,D_937] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_934),u1_struct_0(B_935),C_936,D_937),B_935)
      | ~ v4_pre_topc(D_937,A_934)
      | ~ m1_subset_1(D_937,k1_zfmisc_1(u1_struct_0(A_934)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_934),u1_struct_0(B_935),C_936),B_935,A_934)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_934),u1_struct_0(B_935),C_936),u1_struct_0(B_935),u1_struct_0(A_934))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_934),u1_struct_0(B_935),C_936))
      | ~ l1_pre_topc(A_934)
      | ~ l1_pre_topc(B_935)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_934),u1_struct_0(B_935))))
      | ~ v1_funct_2(C_936,u1_struct_0(A_934),u1_struct_0(B_935))
      | ~ v1_funct_1(C_936)
      | ~ v2_funct_1(C_936)
      | k2_relset_1(u1_struct_0(A_934),u1_struct_0(B_935),C_936) != k2_struct_0(B_935)
      | ~ m1_subset_1(D_937,k1_zfmisc_1(u1_struct_0(A_934)))
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_934),u1_struct_0(B_935))))
      | ~ v1_funct_2(C_936,u1_struct_0(A_934),u1_struct_0(B_935))
      | ~ v1_funct_1(C_936)
      | ~ l1_struct_0(B_935)
      | ~ l1_struct_0(A_934) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_13827])).

tff(c_14115,plain,(
    ! [D_937] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_937),'#skF_5')
      | ~ v4_pre_topc(D_937,'#skF_4')
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_funct_1('#skF_6')
      | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
      | ~ m1_subset_1(D_937,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13364,c_14107])).

tff(c_14120,plain,(
    ! [D_937] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_937),'#skF_5')
      | ~ v4_pre_topc(D_937,'#skF_4')
      | ~ m1_subset_1(D_937,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_122,c_114,c_72,c_78,c_13354,c_13519,c_14115])).

tff(c_14121,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_14120])).

tff(c_14124,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_14121])).

tff(c_14128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_14124])).

tff(c_14130,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_14120])).

tff(c_14129,plain,(
    ! [D_937] :
      ( ~ l1_struct_0('#skF_5')
      | v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_937),'#skF_5')
      | ~ v4_pre_topc(D_937,'#skF_4')
      | ~ m1_subset_1(D_937,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_14120])).

tff(c_14131,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_14129])).

tff(c_14134,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_14131])).

tff(c_14138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_14134])).

tff(c_14140,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_14129])).

tff(c_13534,plain,(
    ! [A_686,B_687,C_688] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(A_686),u1_struct_0(B_687),C_688),B_687,A_686)
      | ~ v3_tops_2(C_688,A_686,B_687)
      | ~ m1_subset_1(C_688,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_686),u1_struct_0(B_687))))
      | ~ v1_funct_2(C_688,u1_struct_0(A_686),u1_struct_0(B_687))
      | ~ v1_funct_1(C_688)
      | ~ l1_pre_topc(B_687)
      | v2_struct_0(B_687)
      | ~ l1_pre_topc(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_13542,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_13534])).

tff(c_13547,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_68,c_13307,c_13542])).

tff(c_13548,plain,(
    v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_13547])).

tff(c_13614,plain,(
    ! [A_722,B_723,C_724,D_725] :
      ( k8_relset_1(u1_struct_0(A_722),u1_struct_0(B_723),C_724,k2_pre_topc(B_723,D_725)) = k2_pre_topc(A_722,k8_relset_1(u1_struct_0(A_722),u1_struct_0(B_723),C_724,D_725))
      | ~ m1_subset_1(D_725,k1_zfmisc_1(u1_struct_0(B_723)))
      | ~ v3_tops_2(C_724,A_722,B_723)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_722),u1_struct_0(B_723))))
      | ~ v1_funct_2(C_724,u1_struct_0(A_722),u1_struct_0(B_723))
      | ~ v1_funct_1(C_724)
      | ~ l1_pre_topc(B_723)
      | ~ v2_pre_topc(B_723)
      | ~ l1_pre_topc(A_722)
      | ~ v2_pre_topc(A_722)
      | v2_struct_0(A_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_13872,plain,(
    ! [A_867,B_868,C_869,D_870] :
      ( k8_relset_1(u1_struct_0(A_867),u1_struct_0(B_868),k2_tops_2(u1_struct_0(B_868),u1_struct_0(A_867),C_869),k2_pre_topc(B_868,D_870)) = k2_pre_topc(A_867,k8_relset_1(u1_struct_0(A_867),u1_struct_0(B_868),k2_tops_2(u1_struct_0(B_868),u1_struct_0(A_867),C_869),D_870))
      | ~ m1_subset_1(D_870,k1_zfmisc_1(u1_struct_0(B_868)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_868),u1_struct_0(A_867),C_869),A_867,B_868)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_868),u1_struct_0(A_867),C_869),u1_struct_0(A_867),u1_struct_0(B_868))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_868),u1_struct_0(A_867),C_869))
      | ~ l1_pre_topc(B_868)
      | ~ v2_pre_topc(B_868)
      | ~ l1_pre_topc(A_867)
      | ~ v2_pre_topc(A_867)
      | v2_struct_0(A_867)
      | ~ m1_subset_1(C_869,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_868),u1_struct_0(A_867))))
      | ~ v1_funct_2(C_869,u1_struct_0(B_868),u1_struct_0(A_867))
      | ~ v1_funct_1(C_869) ) ),
    inference(resolution,[status(thm)],[c_38,c_13614])).

tff(c_15285,plain,(
    ! [B_1058,A_1059,C_1060,D_1061] :
      ( k8_relset_1(u1_struct_0(B_1058),u1_struct_0(A_1059),k2_tops_2(u1_struct_0(A_1059),u1_struct_0(B_1058),C_1060),k2_pre_topc(A_1059,D_1061)) = k2_pre_topc(B_1058,k7_relset_1(u1_struct_0(A_1059),u1_struct_0(B_1058),C_1060,D_1061))
      | ~ m1_subset_1(D_1061,k1_zfmisc_1(u1_struct_0(A_1059)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_1059),u1_struct_0(B_1058),C_1060),B_1058,A_1059)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_1059),u1_struct_0(B_1058),C_1060),u1_struct_0(B_1058),u1_struct_0(A_1059))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_1059),u1_struct_0(B_1058),C_1060))
      | ~ l1_pre_topc(A_1059)
      | ~ v2_pre_topc(A_1059)
      | ~ l1_pre_topc(B_1058)
      | ~ v2_pre_topc(B_1058)
      | v2_struct_0(B_1058)
      | ~ m1_subset_1(C_1060,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1059),u1_struct_0(B_1058))))
      | ~ v1_funct_2(C_1060,u1_struct_0(A_1059),u1_struct_0(B_1058))
      | ~ v1_funct_1(C_1060)
      | ~ v2_funct_1(C_1060)
      | k2_relset_1(u1_struct_0(A_1059),u1_struct_0(B_1058),C_1060) != k2_struct_0(B_1058)
      | ~ m1_subset_1(D_1061,k1_zfmisc_1(u1_struct_0(A_1059)))
      | ~ m1_subset_1(C_1060,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1059),u1_struct_0(B_1058))))
      | ~ v1_funct_2(C_1060,u1_struct_0(A_1059),u1_struct_0(B_1058))
      | ~ v1_funct_1(C_1060)
      | ~ l1_struct_0(B_1058)
      | ~ l1_struct_0(A_1059) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_13872])).

tff(c_39407,plain,(
    ! [A_1978,B_1979,C_1980,D_1981] :
      ( k7_relset_1(u1_struct_0(A_1978),u1_struct_0(B_1979),C_1980,k2_pre_topc(A_1978,D_1981)) = k2_pre_topc(B_1979,k7_relset_1(u1_struct_0(A_1978),u1_struct_0(B_1979),C_1980,D_1981))
      | ~ m1_subset_1(D_1981,k1_zfmisc_1(u1_struct_0(A_1978)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_1978),u1_struct_0(B_1979),C_1980),B_1979,A_1978)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_1978),u1_struct_0(B_1979),C_1980),u1_struct_0(B_1979),u1_struct_0(A_1978))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_1978),u1_struct_0(B_1979),C_1980))
      | ~ l1_pre_topc(A_1978)
      | ~ v2_pre_topc(A_1978)
      | ~ l1_pre_topc(B_1979)
      | ~ v2_pre_topc(B_1979)
      | v2_struct_0(B_1979)
      | ~ m1_subset_1(C_1980,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1978),u1_struct_0(B_1979))))
      | ~ v1_funct_2(C_1980,u1_struct_0(A_1978),u1_struct_0(B_1979))
      | ~ v1_funct_1(C_1980)
      | ~ v2_funct_1(C_1980)
      | k2_relset_1(u1_struct_0(A_1978),u1_struct_0(B_1979),C_1980) != k2_struct_0(B_1979)
      | ~ m1_subset_1(D_1981,k1_zfmisc_1(u1_struct_0(A_1978)))
      | ~ m1_subset_1(C_1980,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1978),u1_struct_0(B_1979))))
      | ~ v1_funct_2(C_1980,u1_struct_0(A_1978),u1_struct_0(B_1979))
      | ~ v1_funct_1(C_1980)
      | ~ l1_struct_0(B_1979)
      | ~ l1_struct_0(A_1978)
      | ~ v2_funct_1(C_1980)
      | k2_relset_1(u1_struct_0(A_1978),u1_struct_0(B_1979),C_1980) != k2_struct_0(B_1979)
      | ~ m1_subset_1(k2_pre_topc(A_1978,D_1981),k1_zfmisc_1(u1_struct_0(A_1978)))
      | ~ m1_subset_1(C_1980,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1978),u1_struct_0(B_1979))))
      | ~ v1_funct_2(C_1980,u1_struct_0(A_1978),u1_struct_0(B_1979))
      | ~ v1_funct_1(C_1980)
      | ~ l1_struct_0(B_1979)
      | ~ l1_struct_0(A_1978) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_15285])).

tff(c_39415,plain,(
    ! [D_1981] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',D_1981)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_1981))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(D_1981,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_funct_1('#skF_6')
      | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_1981),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13364,c_39407])).

tff(c_39420,plain,(
    ! [D_1981] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',D_1981)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_1981))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(D_1981,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_1981),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14130,c_14140,c_70,c_68,c_66,c_122,c_114,c_74,c_72,c_80,c_78,c_13354,c_13548,c_39415])).

tff(c_39422,plain,(
    ! [D_1982] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',D_1982)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_1982))
      | ~ m1_subset_1(D_1982,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_1982),k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_39420])).

tff(c_39622,plain,(
    ! [B_30] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',B_30)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_39422])).

tff(c_39735,plain,(
    ! [B_1983] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',B_1983)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',B_1983))
      | ~ m1_subset_1(B_1983,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_39622])).

tff(c_84,plain,
    ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4','#skF_7')) != k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7'))
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_13389,plain,(
    k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4','#skF_7')) != k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13307,c_127,c_122,c_114,c_84])).

tff(c_40706,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_39735,c_13389])).

tff(c_40892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13306,c_40706])).

tff(c_40893,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_40896,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40893,c_122,c_114,c_86])).

tff(c_40897,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40896])).

tff(c_41046,plain,(
    ! [A_2028,B_2029,C_2030] :
      ( k1_relset_1(u1_struct_0(A_2028),u1_struct_0(B_2029),C_2030) = k2_struct_0(A_2028)
      | ~ v3_tops_2(C_2030,A_2028,B_2029)
      | ~ m1_subset_1(C_2030,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2028),u1_struct_0(B_2029))))
      | ~ v1_funct_2(C_2030,u1_struct_0(A_2028),u1_struct_0(B_2029))
      | ~ v1_funct_1(C_2030)
      | ~ l1_pre_topc(B_2029)
      | ~ l1_pre_topc(A_2028) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_41057,plain,
    ( k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_41046])).

tff(c_41062,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_68,c_40893,c_41057])).

tff(c_41064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40897,c_41062])).

tff(c_41066,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_40896])).

tff(c_40894,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_41072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41066,c_40894])).

tff(c_41074,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_41073,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_41231,plain,(
    ! [A_2075,B_2076,C_2077] :
      ( k2_relset_1(u1_struct_0(A_2075),u1_struct_0(B_2076),C_2077) = k2_struct_0(B_2076)
      | ~ v3_tops_2(C_2077,A_2075,B_2076)
      | ~ m1_subset_1(C_2077,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2075),u1_struct_0(B_2076))))
      | ~ v1_funct_2(C_2077,u1_struct_0(A_2075),u1_struct_0(B_2076))
      | ~ v1_funct_1(C_2077)
      | ~ l1_pre_topc(B_2076)
      | ~ l1_pre_topc(A_2075) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_41242,plain,
    ( k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_41231])).

tff(c_41247,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_68,c_41073,c_41242])).

tff(c_41249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41074,c_41247])).

tff(c_41251,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_41250,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_41324,plain,(
    ! [C_2103,A_2104,B_2105] :
      ( v2_funct_1(C_2103)
      | ~ v3_tops_2(C_2103,A_2104,B_2105)
      | ~ m1_subset_1(C_2103,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2104),u1_struct_0(B_2105))))
      | ~ v1_funct_2(C_2103,u1_struct_0(A_2104),u1_struct_0(B_2105))
      | ~ v1_funct_1(C_2103)
      | ~ l1_pre_topc(B_2105)
      | ~ l1_pre_topc(A_2104) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_41335,plain,
    ( v2_funct_1('#skF_6')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_41324])).

tff(c_41340,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_70,c_68,c_41250,c_41335])).

tff(c_41342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41251,c_41340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:50:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.88/31.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.88/31.64  
% 50.88/31.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 50.88/31.64  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 50.88/31.64  
% 50.88/31.64  %Foreground sorts:
% 50.88/31.64  
% 50.88/31.64  
% 50.88/31.64  %Background operators:
% 50.88/31.64  
% 50.88/31.64  
% 50.88/31.64  %Foreground operators:
% 50.88/31.64  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 50.88/31.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 50.88/31.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 50.88/31.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 50.88/31.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 50.88/31.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.88/31.64  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 50.88/31.64  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 50.88/31.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 50.88/31.64  tff('#skF_7', type, '#skF_7': $i).
% 50.88/31.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 50.88/31.64  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 50.88/31.64  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 50.88/31.64  tff('#skF_5', type, '#skF_5': $i).
% 50.88/31.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 50.88/31.64  tff('#skF_6', type, '#skF_6': $i).
% 50.88/31.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 50.88/31.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 50.88/31.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 50.88/31.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 50.88/31.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 50.88/31.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.88/31.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 50.88/31.64  tff('#skF_4', type, '#skF_4': $i).
% 50.88/31.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 50.88/31.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.88/31.64  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 50.88/31.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 50.88/31.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 50.88/31.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 50.88/31.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 50.88/31.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 50.88/31.64  
% 51.13/31.68  tff(f_248, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> ((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(A, D)) = k2_pre_topc(B, k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_2)).
% 51.13/31.68  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 51.13/31.68  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 51.13/31.68  tff(f_117, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 51.13/31.68  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_2)).
% 51.13/31.68  tff(f_35, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 51.13/31.68  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 51.13/31.68  tff(f_164, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k8_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tops_2)).
% 51.13/31.68  tff(f_143, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(A, D)), k2_pre_topc(B, k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_tops_2)).
% 51.13/31.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 51.13/31.68  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 51.13/31.68  tff(f_183, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_tops_2)).
% 51.13/31.68  tff(f_215, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> ((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(B, D)) = k2_pre_topc(A, k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_2)).
% 51.13/31.68  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_72, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_20, plain, (![A_31]: (l1_struct_0(A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_66])).
% 51.13/31.68  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_106, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_127, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_106])).
% 51.13/31.68  tff(c_100, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_122, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_100])).
% 51.13/31.68  tff(c_94, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_114, plain, (v2_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_94])).
% 51.13/31.68  tff(c_86, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_135, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_122, c_114, c_86])).
% 51.13/31.68  tff(c_136, plain, (~v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_135])).
% 51.13/31.68  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_68, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_287, plain, (![A_166, B_167, C_168]: (v4_pre_topc('#skF_1'(A_166, B_167, C_168), B_167) | v5_pre_topc(C_168, A_166, B_167) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0(A_166), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_56])).
% 51.13/31.68  tff(c_295, plain, (v4_pre_topc('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_287])).
% 51.13/31.68  tff(c_300, plain, (v4_pre_topc('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_68, c_295])).
% 51.13/31.68  tff(c_301, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_300])).
% 51.13/31.68  tff(c_157, plain, (![A_144, B_145, C_146]: (v1_funct_1(k2_tops_2(A_144, B_145, C_146)) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2(C_146, A_144, B_145) | ~v1_funct_1(C_146))), inference(cnfTransformation, [status(thm)], [f_117])).
% 51.13/31.68  tff(c_164, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_157])).
% 51.13/31.68  tff(c_168, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_164])).
% 51.13/31.68  tff(c_169, plain, (![A_147, B_148, C_149]: (v1_funct_2(k2_tops_2(A_147, B_148, C_149), B_148, A_147) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))) | ~v1_funct_2(C_149, A_147, B_148) | ~v1_funct_1(C_149))), inference(cnfTransformation, [status(thm)], [f_117])).
% 51.13/31.68  tff(c_174, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_169])).
% 51.13/31.68  tff(c_178, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_174])).
% 51.13/31.68  tff(c_38, plain, (![A_42, B_43, C_44]: (m1_subset_1(k2_tops_2(A_42, B_43, C_44), k1_zfmisc_1(k2_zfmisc_1(B_43, A_42))) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(C_44, A_42, B_43) | ~v1_funct_1(C_44))), inference(cnfTransformation, [status(thm)], [f_117])).
% 51.13/31.68  tff(c_1405, plain, (![A_299, B_300, C_301]: (v4_pre_topc('#skF_1'(A_299, B_300, k2_tops_2(u1_struct_0(B_300), u1_struct_0(A_299), C_301)), B_300) | v5_pre_topc(k2_tops_2(u1_struct_0(B_300), u1_struct_0(A_299), C_301), A_299, B_300) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_300), u1_struct_0(A_299), C_301), u1_struct_0(A_299), u1_struct_0(B_300)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_300), u1_struct_0(A_299), C_301)) | ~l1_pre_topc(B_300) | ~l1_pre_topc(A_299) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_300), u1_struct_0(A_299)))) | ~v1_funct_2(C_301, u1_struct_0(B_300), u1_struct_0(A_299)) | ~v1_funct_1(C_301))), inference(resolution, [status(thm)], [c_38, c_287])).
% 51.13/31.68  tff(c_1413, plain, (v4_pre_topc('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), '#skF_4') | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_178, c_1405])).
% 51.13/31.68  tff(c_1418, plain, (v4_pre_topc('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), '#skF_4') | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_72, c_78, c_168, c_1413])).
% 51.13/31.68  tff(c_1419, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1418])).
% 51.13/31.68  tff(c_26, plain, (![C_41, A_35, B_39]: (v3_tops_2(C_41, A_35, B_39) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_35), u1_struct_0(B_39), C_41), B_39, A_35) | ~v5_pre_topc(C_41, A_35, B_39) | ~v2_funct_1(C_41) | k2_relset_1(u1_struct_0(A_35), u1_struct_0(B_39), C_41)!=k2_struct_0(B_39) | k1_relset_1(u1_struct_0(A_35), u1_struct_0(B_39), C_41)!=k2_struct_0(A_35) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_35), u1_struct_0(B_39)))) | ~v1_funct_2(C_41, u1_struct_0(A_35), u1_struct_0(B_39)) | ~v1_funct_1(C_41) | ~l1_pre_topc(B_39) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_105])).
% 51.13/31.68  tff(c_1421, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1419, c_26])).
% 51.13/31.68  tff(c_1424, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_68, c_66, c_127, c_122, c_114, c_301, c_1421])).
% 51.13/31.68  tff(c_1426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_1424])).
% 51.13/31.68  tff(c_1428, plain, (~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1418])).
% 51.13/31.68  tff(c_313, plain, (![A_175, B_176, C_177]: (m1_subset_1('#skF_1'(A_175, B_176, C_177), k1_zfmisc_1(u1_struct_0(B_176))) | v5_pre_topc(C_177, A_175, B_176) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_175), u1_struct_0(B_176)))) | ~v1_funct_2(C_177, u1_struct_0(A_175), u1_struct_0(B_176)) | ~v1_funct_1(C_177) | ~l1_pre_topc(B_176) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_56])).
% 51.13/31.68  tff(c_322, plain, (![A_175, B_176, C_44]: (m1_subset_1('#skF_1'(A_175, B_176, k2_tops_2(u1_struct_0(B_176), u1_struct_0(A_175), C_44)), k1_zfmisc_1(u1_struct_0(B_176))) | v5_pre_topc(k2_tops_2(u1_struct_0(B_176), u1_struct_0(A_175), C_44), A_175, B_176) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_176), u1_struct_0(A_175), C_44), u1_struct_0(A_175), u1_struct_0(B_176)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_176), u1_struct_0(A_175), C_44)) | ~l1_pre_topc(B_176) | ~l1_pre_topc(A_175) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_176), u1_struct_0(A_175)))) | ~v1_funct_2(C_44, u1_struct_0(B_176), u1_struct_0(A_175)) | ~v1_funct_1(C_44))), inference(resolution, [status(thm)], [c_38, c_313])).
% 51.13/31.68  tff(c_74, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_8, plain, (![A_3, B_4, C_5, D_6]: (m1_subset_1(k7_relset_1(A_3, B_4, C_5, D_6), k1_zfmisc_1(B_4)) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 51.13/31.68  tff(c_147, plain, (![B_142, A_143]: (v4_pre_topc(B_142, A_143) | k2_pre_topc(A_143, B_142)!=B_142 | ~v2_pre_topc(A_143) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_81])).
% 51.13/31.68  tff(c_388, plain, (![A_190, A_191, C_192, D_193]: (v4_pre_topc(k7_relset_1(A_190, u1_struct_0(A_191), C_192, D_193), A_191) | k2_pre_topc(A_191, k7_relset_1(A_190, u1_struct_0(A_191), C_192, D_193))!=k7_relset_1(A_190, u1_struct_0(A_191), C_192, D_193) | ~v2_pre_topc(A_191) | ~l1_pre_topc(A_191) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, u1_struct_0(A_191)))))), inference(resolution, [status(thm)], [c_8, c_147])).
% 51.13/31.68  tff(c_396, plain, (![D_193]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_193), '#skF_5') | k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_193))!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_193) | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_388])).
% 51.13/31.68  tff(c_401, plain, (![D_193]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_193), '#skF_5') | k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_193))!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_193))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_396])).
% 51.13/31.68  tff(c_726, plain, (![B_242, A_243, C_244, D_245]: (k8_relset_1(u1_struct_0(B_242), u1_struct_0(A_243), k2_tops_2(u1_struct_0(A_243), u1_struct_0(B_242), C_244), D_245)=k7_relset_1(u1_struct_0(A_243), u1_struct_0(B_242), C_244, D_245) | ~v2_funct_1(C_244) | k2_relset_1(u1_struct_0(A_243), u1_struct_0(B_242), C_244)!=k2_struct_0(B_242) | ~m1_subset_1(D_245, k1_zfmisc_1(u1_struct_0(A_243))) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_243), u1_struct_0(B_242)))) | ~v1_funct_2(C_244, u1_struct_0(A_243), u1_struct_0(B_242)) | ~v1_funct_1(C_244) | ~l1_struct_0(B_242) | ~l1_struct_0(A_243))), inference(cnfTransformation, [status(thm)], [f_164])).
% 51.13/31.68  tff(c_12, plain, (![A_7, B_19, C_25]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_7), u1_struct_0(B_19), C_25, '#skF_1'(A_7, B_19, C_25)), A_7) | v5_pre_topc(C_25, A_7, B_19) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7), u1_struct_0(B_19)))) | ~v1_funct_2(C_25, u1_struct_0(A_7), u1_struct_0(B_19)) | ~v1_funct_1(C_25) | ~l1_pre_topc(B_19) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 51.13/31.68  tff(c_9325, plain, (![A_495, B_496, C_497]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_495), u1_struct_0(B_496), C_497, '#skF_1'(B_496, A_495, k2_tops_2(u1_struct_0(A_495), u1_struct_0(B_496), C_497))), B_496) | v5_pre_topc(k2_tops_2(u1_struct_0(A_495), u1_struct_0(B_496), C_497), B_496, A_495) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_495), u1_struct_0(B_496), C_497), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_496), u1_struct_0(A_495)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_495), u1_struct_0(B_496), C_497), u1_struct_0(B_496), u1_struct_0(A_495)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_495), u1_struct_0(B_496), C_497)) | ~l1_pre_topc(A_495) | ~l1_pre_topc(B_496) | ~v2_funct_1(C_497) | k2_relset_1(u1_struct_0(A_495), u1_struct_0(B_496), C_497)!=k2_struct_0(B_496) | ~m1_subset_1('#skF_1'(B_496, A_495, k2_tops_2(u1_struct_0(A_495), u1_struct_0(B_496), C_497)), k1_zfmisc_1(u1_struct_0(A_495))) | ~m1_subset_1(C_497, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_495), u1_struct_0(B_496)))) | ~v1_funct_2(C_497, u1_struct_0(A_495), u1_struct_0(B_496)) | ~v1_funct_1(C_497) | ~l1_struct_0(B_496) | ~l1_struct_0(A_495))), inference(superposition, [status(thm), theory('equality')], [c_726, c_12])).
% 51.13/31.68  tff(c_9337, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), inference(resolution, [status(thm)], [c_401, c_9325])).
% 51.13/31.68  tff(c_9342, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_122, c_114, c_72, c_78, c_168, c_178, c_9337])).
% 51.13/31.68  tff(c_9343, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_1428, c_9342])).
% 51.13/31.68  tff(c_9344, plain, (k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))!=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), inference(splitLeft, [status(thm)], [c_9343])).
% 51.13/31.68  tff(c_1427, plain, (v4_pre_topc('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), '#skF_4')), inference(splitRight, [status(thm)], [c_1418])).
% 51.13/31.68  tff(c_1497, plain, (![A_315, B_316, C_317]: (m1_subset_1('#skF_1'(A_315, B_316, k2_tops_2(u1_struct_0(B_316), u1_struct_0(A_315), C_317)), k1_zfmisc_1(u1_struct_0(B_316))) | v5_pre_topc(k2_tops_2(u1_struct_0(B_316), u1_struct_0(A_315), C_317), A_315, B_316) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_316), u1_struct_0(A_315), C_317), u1_struct_0(A_315), u1_struct_0(B_316)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_316), u1_struct_0(A_315), C_317)) | ~l1_pre_topc(B_316) | ~l1_pre_topc(A_315) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_316), u1_struct_0(A_315)))) | ~v1_funct_2(C_317, u1_struct_0(B_316), u1_struct_0(A_315)) | ~v1_funct_1(C_317))), inference(resolution, [status(thm)], [c_38, c_313])).
% 51.13/31.68  tff(c_24, plain, (![A_32, B_34]: (k2_pre_topc(A_32, B_34)=B_34 | ~v4_pre_topc(B_34, A_32) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_81])).
% 51.13/31.68  tff(c_12074, plain, (![B_525, A_526, C_527]: (k2_pre_topc(B_525, '#skF_1'(A_526, B_525, k2_tops_2(u1_struct_0(B_525), u1_struct_0(A_526), C_527)))='#skF_1'(A_526, B_525, k2_tops_2(u1_struct_0(B_525), u1_struct_0(A_526), C_527)) | ~v4_pre_topc('#skF_1'(A_526, B_525, k2_tops_2(u1_struct_0(B_525), u1_struct_0(A_526), C_527)), B_525) | v5_pre_topc(k2_tops_2(u1_struct_0(B_525), u1_struct_0(A_526), C_527), A_526, B_525) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_525), u1_struct_0(A_526), C_527), u1_struct_0(A_526), u1_struct_0(B_525)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_525), u1_struct_0(A_526), C_527)) | ~l1_pre_topc(B_525) | ~l1_pre_topc(A_526) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_525), u1_struct_0(A_526)))) | ~v1_funct_2(C_527, u1_struct_0(B_525), u1_struct_0(A_526)) | ~v1_funct_1(C_527))), inference(resolution, [status(thm)], [c_1497, c_24])).
% 51.13/31.68  tff(c_12076, plain, (k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))='#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_1427, c_12074])).
% 51.13/31.68  tff(c_12079, plain, (k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))='#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_72, c_78, c_168, c_178, c_12076])).
% 51.13/31.68  tff(c_12080, plain, (k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))='#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1428, c_12079])).
% 51.13/31.68  tff(c_88, plain, (![D_129]: (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', D_129))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_129)) | ~m1_subset_1(D_129, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_188, plain, (![D_129]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', D_129))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_129)) | ~m1_subset_1(D_129, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_136, c_88])).
% 51.13/31.68  tff(c_12339, plain, (k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))=k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_12080, c_188])).
% 51.13/31.68  tff(c_12441, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_9344, c_12339])).
% 51.13/31.68  tff(c_12449, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_322, c_12441])).
% 51.13/31.68  tff(c_12452, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_72, c_78, c_168, c_178, c_12449])).
% 51.13/31.68  tff(c_12454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1428, c_12452])).
% 51.13/31.68  tff(c_12455, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_9343])).
% 51.13/31.68  tff(c_12457, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_12455])).
% 51.13/31.68  tff(c_12473, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_12457])).
% 51.13/31.68  tff(c_12477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_12473])).
% 51.13/31.68  tff(c_12479, plain, (m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_12455])).
% 51.13/31.68  tff(c_16, plain, (![A_7, B_19, C_25]: (m1_subset_1('#skF_1'(A_7, B_19, C_25), k1_zfmisc_1(u1_struct_0(B_19))) | v5_pre_topc(C_25, A_7, B_19) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7), u1_struct_0(B_19)))) | ~v1_funct_2(C_25, u1_struct_0(A_7), u1_struct_0(B_19)) | ~v1_funct_1(C_25) | ~l1_pre_topc(B_19) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 51.13/31.68  tff(c_12503, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12479, c_16])).
% 51.13/31.68  tff(c_12552, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_78, c_168, c_178, c_12503])).
% 51.13/31.68  tff(c_12553, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1428, c_12552])).
% 51.13/31.68  tff(c_12478, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_12455])).
% 51.13/31.68  tff(c_12618, plain, (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12553, c_12478])).
% 51.13/31.68  tff(c_12619, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_12618])).
% 51.13/31.68  tff(c_12634, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_12619])).
% 51.13/31.68  tff(c_12638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_12634])).
% 51.13/31.68  tff(c_12639, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_12618])).
% 51.13/31.68  tff(c_12643, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_12639])).
% 51.13/31.68  tff(c_12647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_12643])).
% 51.13/31.68  tff(c_12649, plain, (~v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_300])).
% 51.13/31.68  tff(c_80, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_12869, plain, (![A_578, B_579, C_580]: (m1_subset_1('#skF_2'(A_578, B_579, C_580), k1_zfmisc_1(u1_struct_0(A_578))) | v5_pre_topc(C_580, A_578, B_579) | ~m1_subset_1(C_580, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_578), u1_struct_0(B_579)))) | ~v1_funct_2(C_580, u1_struct_0(A_578), u1_struct_0(B_579)) | ~v1_funct_1(C_580) | ~l1_pre_topc(B_579) | ~v2_pre_topc(B_579) | v2_struct_0(B_579) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578))), inference(cnfTransformation, [status(thm)], [f_143])).
% 51.13/31.68  tff(c_12877, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_12869])).
% 51.13/31.68  tff(c_12882, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_70, c_68, c_12877])).
% 51.13/31.68  tff(c_12883, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_12649, c_12882])).
% 51.13/31.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 51.13/31.68  tff(c_13292, plain, (![A_632, B_633, C_634]: (~r1_tarski(k7_relset_1(u1_struct_0(A_632), u1_struct_0(B_633), C_634, k2_pre_topc(A_632, '#skF_2'(A_632, B_633, C_634))), k2_pre_topc(B_633, k7_relset_1(u1_struct_0(A_632), u1_struct_0(B_633), C_634, '#skF_2'(A_632, B_633, C_634)))) | v5_pre_topc(C_634, A_632, B_633) | ~m1_subset_1(C_634, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_632), u1_struct_0(B_633)))) | ~v1_funct_2(C_634, u1_struct_0(A_632), u1_struct_0(B_633)) | ~v1_funct_1(C_634) | ~l1_pre_topc(B_633) | ~v2_pre_topc(B_633) | v2_struct_0(B_633) | ~l1_pre_topc(A_632) | ~v2_pre_topc(A_632))), inference(cnfTransformation, [status(thm)], [f_143])).
% 51.13/31.68  tff(c_13300, plain, (~r1_tarski(k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_6'))), k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_6')))) | v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_13292])).
% 51.13/31.68  tff(c_13303, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12883, c_80, c_78, c_74, c_72, c_70, c_68, c_66, c_6, c_13300])).
% 51.13/31.68  tff(c_13305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_12649, c_13303])).
% 51.13/31.68  tff(c_13306, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_135])).
% 51.13/31.68  tff(c_18, plain, (![A_29, B_30]: (m1_subset_1(k2_pre_topc(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_62])).
% 51.13/31.68  tff(c_13343, plain, (![A_639, B_640, C_641]: (v1_funct_1(k2_tops_2(A_639, B_640, C_641)) | ~m1_subset_1(C_641, k1_zfmisc_1(k2_zfmisc_1(A_639, B_640))) | ~v1_funct_2(C_641, A_639, B_640) | ~v1_funct_1(C_641))), inference(cnfTransformation, [status(thm)], [f_117])).
% 51.13/31.68  tff(c_13350, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_13343])).
% 51.13/31.68  tff(c_13354, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_13350])).
% 51.13/31.68  tff(c_13307, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_135])).
% 51.13/31.68  tff(c_13506, plain, (![A_679, B_680, C_681]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_679), u1_struct_0(B_680), C_681), B_680, A_679) | ~v3_tops_2(C_681, A_679, B_680) | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_679), u1_struct_0(B_680)))) | ~v1_funct_2(C_681, u1_struct_0(A_679), u1_struct_0(B_680)) | ~v1_funct_1(C_681) | ~l1_pre_topc(B_680) | ~l1_pre_topc(A_679))), inference(cnfTransformation, [status(thm)], [f_105])).
% 51.13/31.68  tff(c_13514, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_13506])).
% 51.13/31.68  tff(c_13519, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_68, c_13307, c_13514])).
% 51.13/31.68  tff(c_13355, plain, (![A_642, B_643, C_644]: (v1_funct_2(k2_tops_2(A_642, B_643, C_644), B_643, A_642) | ~m1_subset_1(C_644, k1_zfmisc_1(k2_zfmisc_1(A_642, B_643))) | ~v1_funct_2(C_644, A_642, B_643) | ~v1_funct_1(C_644))), inference(cnfTransformation, [status(thm)], [f_117])).
% 51.13/31.68  tff(c_13360, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_13355])).
% 51.13/31.68  tff(c_13364, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_13360])).
% 51.13/31.68  tff(c_50, plain, (![B_75, A_67, C_79, D_81]: (k8_relset_1(u1_struct_0(B_75), u1_struct_0(A_67), k2_tops_2(u1_struct_0(A_67), u1_struct_0(B_75), C_79), D_81)=k7_relset_1(u1_struct_0(A_67), u1_struct_0(B_75), C_79, D_81) | ~v2_funct_1(C_79) | k2_relset_1(u1_struct_0(A_67), u1_struct_0(B_75), C_79)!=k2_struct_0(B_75) | ~m1_subset_1(D_81, k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_67), u1_struct_0(B_75)))) | ~v1_funct_2(C_79, u1_struct_0(A_67), u1_struct_0(B_75)) | ~v1_funct_1(C_79) | ~l1_struct_0(B_75) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_164])).
% 51.13/31.68  tff(c_13588, plain, (![A_713, B_714, C_715, D_716]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_713), u1_struct_0(B_714), C_715, D_716), A_713) | ~v4_pre_topc(D_716, B_714) | ~m1_subset_1(D_716, k1_zfmisc_1(u1_struct_0(B_714))) | ~v5_pre_topc(C_715, A_713, B_714) | ~m1_subset_1(C_715, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_713), u1_struct_0(B_714)))) | ~v1_funct_2(C_715, u1_struct_0(A_713), u1_struct_0(B_714)) | ~v1_funct_1(C_715) | ~l1_pre_topc(B_714) | ~l1_pre_topc(A_713))), inference(cnfTransformation, [status(thm)], [f_56])).
% 51.13/31.68  tff(c_13827, plain, (![A_834, B_835, C_836, D_837]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_834), u1_struct_0(B_835), k2_tops_2(u1_struct_0(B_835), u1_struct_0(A_834), C_836), D_837), A_834) | ~v4_pre_topc(D_837, B_835) | ~m1_subset_1(D_837, k1_zfmisc_1(u1_struct_0(B_835))) | ~v5_pre_topc(k2_tops_2(u1_struct_0(B_835), u1_struct_0(A_834), C_836), A_834, B_835) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_835), u1_struct_0(A_834), C_836), u1_struct_0(A_834), u1_struct_0(B_835)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_835), u1_struct_0(A_834), C_836)) | ~l1_pre_topc(B_835) | ~l1_pre_topc(A_834) | ~m1_subset_1(C_836, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_835), u1_struct_0(A_834)))) | ~v1_funct_2(C_836, u1_struct_0(B_835), u1_struct_0(A_834)) | ~v1_funct_1(C_836))), inference(resolution, [status(thm)], [c_38, c_13588])).
% 51.13/31.68  tff(c_14107, plain, (![A_934, B_935, C_936, D_937]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_934), u1_struct_0(B_935), C_936, D_937), B_935) | ~v4_pre_topc(D_937, A_934) | ~m1_subset_1(D_937, k1_zfmisc_1(u1_struct_0(A_934))) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_934), u1_struct_0(B_935), C_936), B_935, A_934) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_934), u1_struct_0(B_935), C_936), u1_struct_0(B_935), u1_struct_0(A_934)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_934), u1_struct_0(B_935), C_936)) | ~l1_pre_topc(A_934) | ~l1_pre_topc(B_935) | ~m1_subset_1(C_936, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_934), u1_struct_0(B_935)))) | ~v1_funct_2(C_936, u1_struct_0(A_934), u1_struct_0(B_935)) | ~v1_funct_1(C_936) | ~v2_funct_1(C_936) | k2_relset_1(u1_struct_0(A_934), u1_struct_0(B_935), C_936)!=k2_struct_0(B_935) | ~m1_subset_1(D_937, k1_zfmisc_1(u1_struct_0(A_934))) | ~m1_subset_1(C_936, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_934), u1_struct_0(B_935)))) | ~v1_funct_2(C_936, u1_struct_0(A_934), u1_struct_0(B_935)) | ~v1_funct_1(C_936) | ~l1_struct_0(B_935) | ~l1_struct_0(A_934))), inference(superposition, [status(thm), theory('equality')], [c_50, c_13827])).
% 51.13/31.68  tff(c_14115, plain, (![D_937]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_937), '#skF_5') | ~v4_pre_topc(D_937, '#skF_4') | ~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | ~m1_subset_1(D_937, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_13364, c_14107])).
% 51.13/31.68  tff(c_14120, plain, (![D_937]: (v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_937), '#skF_5') | ~v4_pre_topc(D_937, '#skF_4') | ~m1_subset_1(D_937, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_122, c_114, c_72, c_78, c_13354, c_13519, c_14115])).
% 51.13/31.68  tff(c_14121, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_14120])).
% 51.13/31.68  tff(c_14124, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_14121])).
% 51.13/31.68  tff(c_14128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_14124])).
% 51.13/31.68  tff(c_14130, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_14120])).
% 51.13/31.68  tff(c_14129, plain, (![D_937]: (~l1_struct_0('#skF_5') | v4_pre_topc(k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_937), '#skF_5') | ~v4_pre_topc(D_937, '#skF_4') | ~m1_subset_1(D_937, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_14120])).
% 51.13/31.68  tff(c_14131, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_14129])).
% 51.13/31.68  tff(c_14134, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_20, c_14131])).
% 51.13/31.68  tff(c_14138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_14134])).
% 51.13/31.68  tff(c_14140, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_14129])).
% 51.13/31.68  tff(c_13534, plain, (![A_686, B_687, C_688]: (v3_tops_2(k2_tops_2(u1_struct_0(A_686), u1_struct_0(B_687), C_688), B_687, A_686) | ~v3_tops_2(C_688, A_686, B_687) | ~m1_subset_1(C_688, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_686), u1_struct_0(B_687)))) | ~v1_funct_2(C_688, u1_struct_0(A_686), u1_struct_0(B_687)) | ~v1_funct_1(C_688) | ~l1_pre_topc(B_687) | v2_struct_0(B_687) | ~l1_pre_topc(A_686))), inference(cnfTransformation, [status(thm)], [f_183])).
% 51.13/31.68  tff(c_13542, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_13534])).
% 51.13/31.68  tff(c_13547, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_68, c_13307, c_13542])).
% 51.13/31.68  tff(c_13548, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_13547])).
% 51.13/31.68  tff(c_13614, plain, (![A_722, B_723, C_724, D_725]: (k8_relset_1(u1_struct_0(A_722), u1_struct_0(B_723), C_724, k2_pre_topc(B_723, D_725))=k2_pre_topc(A_722, k8_relset_1(u1_struct_0(A_722), u1_struct_0(B_723), C_724, D_725)) | ~m1_subset_1(D_725, k1_zfmisc_1(u1_struct_0(B_723))) | ~v3_tops_2(C_724, A_722, B_723) | ~m1_subset_1(C_724, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_722), u1_struct_0(B_723)))) | ~v1_funct_2(C_724, u1_struct_0(A_722), u1_struct_0(B_723)) | ~v1_funct_1(C_724) | ~l1_pre_topc(B_723) | ~v2_pre_topc(B_723) | ~l1_pre_topc(A_722) | ~v2_pre_topc(A_722) | v2_struct_0(A_722))), inference(cnfTransformation, [status(thm)], [f_215])).
% 51.13/31.68  tff(c_13872, plain, (![A_867, B_868, C_869, D_870]: (k8_relset_1(u1_struct_0(A_867), u1_struct_0(B_868), k2_tops_2(u1_struct_0(B_868), u1_struct_0(A_867), C_869), k2_pre_topc(B_868, D_870))=k2_pre_topc(A_867, k8_relset_1(u1_struct_0(A_867), u1_struct_0(B_868), k2_tops_2(u1_struct_0(B_868), u1_struct_0(A_867), C_869), D_870)) | ~m1_subset_1(D_870, k1_zfmisc_1(u1_struct_0(B_868))) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_868), u1_struct_0(A_867), C_869), A_867, B_868) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_868), u1_struct_0(A_867), C_869), u1_struct_0(A_867), u1_struct_0(B_868)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_868), u1_struct_0(A_867), C_869)) | ~l1_pre_topc(B_868) | ~v2_pre_topc(B_868) | ~l1_pre_topc(A_867) | ~v2_pre_topc(A_867) | v2_struct_0(A_867) | ~m1_subset_1(C_869, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_868), u1_struct_0(A_867)))) | ~v1_funct_2(C_869, u1_struct_0(B_868), u1_struct_0(A_867)) | ~v1_funct_1(C_869))), inference(resolution, [status(thm)], [c_38, c_13614])).
% 51.13/31.68  tff(c_15285, plain, (![B_1058, A_1059, C_1060, D_1061]: (k8_relset_1(u1_struct_0(B_1058), u1_struct_0(A_1059), k2_tops_2(u1_struct_0(A_1059), u1_struct_0(B_1058), C_1060), k2_pre_topc(A_1059, D_1061))=k2_pre_topc(B_1058, k7_relset_1(u1_struct_0(A_1059), u1_struct_0(B_1058), C_1060, D_1061)) | ~m1_subset_1(D_1061, k1_zfmisc_1(u1_struct_0(A_1059))) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_1059), u1_struct_0(B_1058), C_1060), B_1058, A_1059) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_1059), u1_struct_0(B_1058), C_1060), u1_struct_0(B_1058), u1_struct_0(A_1059)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_1059), u1_struct_0(B_1058), C_1060)) | ~l1_pre_topc(A_1059) | ~v2_pre_topc(A_1059) | ~l1_pre_topc(B_1058) | ~v2_pre_topc(B_1058) | v2_struct_0(B_1058) | ~m1_subset_1(C_1060, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1059), u1_struct_0(B_1058)))) | ~v1_funct_2(C_1060, u1_struct_0(A_1059), u1_struct_0(B_1058)) | ~v1_funct_1(C_1060) | ~v2_funct_1(C_1060) | k2_relset_1(u1_struct_0(A_1059), u1_struct_0(B_1058), C_1060)!=k2_struct_0(B_1058) | ~m1_subset_1(D_1061, k1_zfmisc_1(u1_struct_0(A_1059))) | ~m1_subset_1(C_1060, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1059), u1_struct_0(B_1058)))) | ~v1_funct_2(C_1060, u1_struct_0(A_1059), u1_struct_0(B_1058)) | ~v1_funct_1(C_1060) | ~l1_struct_0(B_1058) | ~l1_struct_0(A_1059))), inference(superposition, [status(thm), theory('equality')], [c_50, c_13872])).
% 51.13/31.68  tff(c_39407, plain, (![A_1978, B_1979, C_1980, D_1981]: (k7_relset_1(u1_struct_0(A_1978), u1_struct_0(B_1979), C_1980, k2_pre_topc(A_1978, D_1981))=k2_pre_topc(B_1979, k7_relset_1(u1_struct_0(A_1978), u1_struct_0(B_1979), C_1980, D_1981)) | ~m1_subset_1(D_1981, k1_zfmisc_1(u1_struct_0(A_1978))) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_1978), u1_struct_0(B_1979), C_1980), B_1979, A_1978) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_1978), u1_struct_0(B_1979), C_1980), u1_struct_0(B_1979), u1_struct_0(A_1978)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_1978), u1_struct_0(B_1979), C_1980)) | ~l1_pre_topc(A_1978) | ~v2_pre_topc(A_1978) | ~l1_pre_topc(B_1979) | ~v2_pre_topc(B_1979) | v2_struct_0(B_1979) | ~m1_subset_1(C_1980, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1978), u1_struct_0(B_1979)))) | ~v1_funct_2(C_1980, u1_struct_0(A_1978), u1_struct_0(B_1979)) | ~v1_funct_1(C_1980) | ~v2_funct_1(C_1980) | k2_relset_1(u1_struct_0(A_1978), u1_struct_0(B_1979), C_1980)!=k2_struct_0(B_1979) | ~m1_subset_1(D_1981, k1_zfmisc_1(u1_struct_0(A_1978))) | ~m1_subset_1(C_1980, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1978), u1_struct_0(B_1979)))) | ~v1_funct_2(C_1980, u1_struct_0(A_1978), u1_struct_0(B_1979)) | ~v1_funct_1(C_1980) | ~l1_struct_0(B_1979) | ~l1_struct_0(A_1978) | ~v2_funct_1(C_1980) | k2_relset_1(u1_struct_0(A_1978), u1_struct_0(B_1979), C_1980)!=k2_struct_0(B_1979) | ~m1_subset_1(k2_pre_topc(A_1978, D_1981), k1_zfmisc_1(u1_struct_0(A_1978))) | ~m1_subset_1(C_1980, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1978), u1_struct_0(B_1979)))) | ~v1_funct_2(C_1980, u1_struct_0(A_1978), u1_struct_0(B_1979)) | ~v1_funct_1(C_1980) | ~l1_struct_0(B_1979) | ~l1_struct_0(A_1978))), inference(superposition, [status(thm), theory('equality')], [c_50, c_15285])).
% 51.13/31.68  tff(c_39415, plain, (![D_1981]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', D_1981))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_1981)) | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(D_1981, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | ~m1_subset_1(k2_pre_topc('#skF_4', D_1981), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_13364, c_39407])).
% 51.13/31.68  tff(c_39420, plain, (![D_1981]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', D_1981))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_1981)) | v2_struct_0('#skF_5') | ~m1_subset_1(D_1981, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_pre_topc('#skF_4', D_1981), k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_14130, c_14140, c_70, c_68, c_66, c_122, c_114, c_74, c_72, c_80, c_78, c_13354, c_13548, c_39415])).
% 51.13/31.68  tff(c_39422, plain, (![D_1982]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', D_1982))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_1982)) | ~m1_subset_1(D_1982, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_pre_topc('#skF_4', D_1982), k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_39420])).
% 51.13/31.68  tff(c_39622, plain, (![B_30]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', B_30))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_39422])).
% 51.13/31.68  tff(c_39735, plain, (![B_1983]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', B_1983))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', B_1983)) | ~m1_subset_1(B_1983, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_39622])).
% 51.13/31.68  tff(c_84, plain, (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', '#skF_7'))!=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_7')) | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_248])).
% 51.13/31.68  tff(c_13389, plain, (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', '#skF_7'))!=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_13307, c_127, c_122, c_114, c_84])).
% 51.13/31.68  tff(c_40706, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_39735, c_13389])).
% 51.13/31.68  tff(c_40892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13306, c_40706])).
% 51.13/31.68  tff(c_40893, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_106])).
% 51.13/31.68  tff(c_40896, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40893, c_122, c_114, c_86])).
% 51.13/31.68  tff(c_40897, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_40896])).
% 51.13/31.68  tff(c_41046, plain, (![A_2028, B_2029, C_2030]: (k1_relset_1(u1_struct_0(A_2028), u1_struct_0(B_2029), C_2030)=k2_struct_0(A_2028) | ~v3_tops_2(C_2030, A_2028, B_2029) | ~m1_subset_1(C_2030, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2028), u1_struct_0(B_2029)))) | ~v1_funct_2(C_2030, u1_struct_0(A_2028), u1_struct_0(B_2029)) | ~v1_funct_1(C_2030) | ~l1_pre_topc(B_2029) | ~l1_pre_topc(A_2028))), inference(cnfTransformation, [status(thm)], [f_105])).
% 51.13/31.68  tff(c_41057, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_41046])).
% 51.13/31.68  tff(c_41062, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_68, c_40893, c_41057])).
% 51.13/31.68  tff(c_41064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40897, c_41062])).
% 51.13/31.68  tff(c_41066, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_40896])).
% 51.13/31.68  tff(c_40894, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_106])).
% 51.13/31.68  tff(c_41072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41066, c_40894])).
% 51.13/31.68  tff(c_41074, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_100])).
% 51.13/31.68  tff(c_41073, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_100])).
% 51.13/31.68  tff(c_41231, plain, (![A_2075, B_2076, C_2077]: (k2_relset_1(u1_struct_0(A_2075), u1_struct_0(B_2076), C_2077)=k2_struct_0(B_2076) | ~v3_tops_2(C_2077, A_2075, B_2076) | ~m1_subset_1(C_2077, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2075), u1_struct_0(B_2076)))) | ~v1_funct_2(C_2077, u1_struct_0(A_2075), u1_struct_0(B_2076)) | ~v1_funct_1(C_2077) | ~l1_pre_topc(B_2076) | ~l1_pre_topc(A_2075))), inference(cnfTransformation, [status(thm)], [f_105])).
% 51.13/31.68  tff(c_41242, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_41231])).
% 51.13/31.68  tff(c_41247, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_68, c_41073, c_41242])).
% 51.13/31.68  tff(c_41249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41074, c_41247])).
% 51.13/31.68  tff(c_41251, plain, (~v2_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_94])).
% 51.13/31.68  tff(c_41250, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_94])).
% 51.13/31.68  tff(c_41324, plain, (![C_2103, A_2104, B_2105]: (v2_funct_1(C_2103) | ~v3_tops_2(C_2103, A_2104, B_2105) | ~m1_subset_1(C_2103, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2104), u1_struct_0(B_2105)))) | ~v1_funct_2(C_2103, u1_struct_0(A_2104), u1_struct_0(B_2105)) | ~v1_funct_1(C_2103) | ~l1_pre_topc(B_2105) | ~l1_pre_topc(A_2104))), inference(cnfTransformation, [status(thm)], [f_105])).
% 51.13/31.68  tff(c_41335, plain, (v2_funct_1('#skF_6') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_41324])).
% 51.13/31.68  tff(c_41340, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_70, c_68, c_41250, c_41335])).
% 51.13/31.68  tff(c_41342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41251, c_41340])).
% 51.13/31.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.13/31.68  
% 51.13/31.68  Inference rules
% 51.13/31.68  ----------------------
% 51.13/31.68  #Ref     : 0
% 51.13/31.68  #Sup     : 11470
% 51.13/31.68  #Fact    : 0
% 51.13/31.68  #Define  : 0
% 51.13/31.68  #Split   : 20
% 51.13/31.68  #Chain   : 0
% 51.13/31.68  #Close   : 0
% 51.13/31.68  
% 51.13/31.68  Ordering : KBO
% 51.13/31.68  
% 51.13/31.68  Simplification rules
% 51.13/31.68  ----------------------
% 51.13/31.68  #Subsume      : 1984
% 51.13/31.68  #Demod        : 5933
% 51.13/31.68  #Tautology    : 1287
% 51.13/31.68  #SimpNegUnit  : 75
% 51.13/31.68  #BackRed      : 0
% 51.13/31.68  
% 51.13/31.68  #Partial instantiations: 0
% 51.13/31.68  #Strategies tried      : 1
% 51.13/31.68  
% 51.13/31.68  Timing (in seconds)
% 51.13/31.68  ----------------------
% 51.20/31.68  Preprocessing        : 0.42
% 51.20/31.68  Parsing              : 0.21
% 51.20/31.68  CNF conversion       : 0.04
% 51.20/31.68  Main loop            : 30.47
% 51.20/31.68  Inferencing          : 6.02
% 51.20/31.68  Reduction            : 6.23
% 51.20/31.68  Demodulation         : 4.76
% 51.20/31.68  BG Simplification    : 0.89
% 51.20/31.68  Subsumption          : 16.69
% 51.20/31.68  Abstraction          : 1.43
% 51.20/31.68  MUC search           : 0.00
% 51.20/31.68  Cooper               : 0.00
% 51.20/31.68  Total                : 30.96
% 51.20/31.68  Index Insertion      : 0.00
% 51.20/31.68  Index Deletion       : 0.00
% 51.20/31.68  Index Matching       : 0.00
% 51.20/31.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
