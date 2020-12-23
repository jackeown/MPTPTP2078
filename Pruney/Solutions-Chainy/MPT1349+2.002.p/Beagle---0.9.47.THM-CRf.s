%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:50 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 8.13s
% Verified   : 
% Statistics : Number of formulae       :  186 (2417 expanded)
%              Number of leaves         :   42 ( 915 expanded)
%              Depth                    :   16
%              Number of atoms          :  786 (16093 expanded)
%              Number of equality atoms :   72 (2802 expanded)
%              Maximal formula depth    :   43 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(f_231,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_2)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => r1_tarski(k2_pre_topc(A,k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D)),k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_pre_topc(B,D))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_147,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

tff(f_126,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).

tff(f_166,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

tff(f_198,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_2)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_98,plain,
    ( v3_tops_2('#skF_6','#skF_4','#skF_5')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_119,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_92,plain,
    ( v3_tops_2('#skF_6','#skF_4','#skF_5')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_114,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_86,plain,
    ( v3_tops_2('#skF_6','#skF_4','#skF_5')
    | v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_106,plain,(
    v2_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_78,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_133,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_114,c_106,c_78])).

tff(c_134,plain,(
    ~ v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_64,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_60,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_66,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_240,plain,(
    ! [A_163,B_164,C_165] :
      ( m1_subset_1('#skF_1'(A_163,B_164,C_165),k1_zfmisc_1(u1_struct_0(B_164)))
      | v5_pre_topc(C_165,A_163,B_164)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_163),u1_struct_0(B_164))))
      | ~ v1_funct_2(C_165,u1_struct_0(A_163),u1_struct_0(B_164))
      | ~ v1_funct_1(C_165)
      | ~ l1_pre_topc(B_164)
      | ~ v2_pre_topc(B_164)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_245,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_240])).

tff(c_249,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_245])).

tff(c_250,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_10,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_125,plain,(
    ! [A_129,B_130,C_131] :
      ( v1_funct_1(k2_tops_2(A_129,B_130,C_131))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_2(C_131,A_129,B_130)
      | ~ v1_funct_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_131,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_128])).

tff(c_135,plain,(
    ! [A_132,B_133,C_134] :
      ( v1_funct_2(k2_tops_2(A_132,B_133,C_134),B_133,A_132)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_2(C_134,A_132,B_133)
      | ~ v1_funct_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_137,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_135])).

tff(c_140,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_137])).

tff(c_80,plain,(
    ! [D_122] :
      ( v3_tops_2('#skF_6','#skF_4','#skF_5')
      | k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',D_122)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_122))
      | ~ m1_subset_1(D_122,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_161,plain,(
    ! [D_122] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',D_122)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_122))
      | ~ m1_subset_1(D_122,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_80])).

tff(c_285,plain,(
    ! [B_183,A_184,C_185,D_186] :
      ( k8_relset_1(u1_struct_0(B_183),u1_struct_0(A_184),k2_tops_2(u1_struct_0(A_184),u1_struct_0(B_183),C_185),D_186) = k7_relset_1(u1_struct_0(A_184),u1_struct_0(B_183),C_185,D_186)
      | ~ v2_funct_1(C_185)
      | k2_relset_1(u1_struct_0(A_184),u1_struct_0(B_183),C_185) != k2_struct_0(B_183)
      | ~ m1_subset_1(D_186,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_184),u1_struct_0(B_183))))
      | ~ v1_funct_2(C_185,u1_struct_0(A_184),u1_struct_0(B_183))
      | ~ v1_funct_1(C_185)
      | ~ l1_struct_0(B_183)
      | ~ l1_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    ! [A_16,B_28,C_34,D_37] :
      ( r1_tarski(k2_pre_topc(A_16,k8_relset_1(u1_struct_0(A_16),u1_struct_0(B_28),C_34,D_37)),k8_relset_1(u1_struct_0(A_16),u1_struct_0(B_28),C_34,k2_pre_topc(B_28,D_37)))
      | ~ m1_subset_1(D_37,k1_zfmisc_1(u1_struct_0(B_28)))
      | ~ v5_pre_topc(C_34,A_16,B_28)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16),u1_struct_0(B_28))))
      | ~ v1_funct_2(C_34,u1_struct_0(A_16),u1_struct_0(B_28))
      | ~ v1_funct_1(C_34)
      | ~ l1_pre_topc(B_28)
      | ~ v2_pre_topc(B_28)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1541,plain,(
    ! [B_273,A_274,C_275,D_276] :
      ( r1_tarski(k2_pre_topc(B_273,k7_relset_1(u1_struct_0(A_274),u1_struct_0(B_273),C_275,D_276)),k8_relset_1(u1_struct_0(B_273),u1_struct_0(A_274),k2_tops_2(u1_struct_0(A_274),u1_struct_0(B_273),C_275),k2_pre_topc(A_274,D_276)))
      | ~ m1_subset_1(D_276,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_274),u1_struct_0(B_273),C_275),B_273,A_274)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_274),u1_struct_0(B_273),C_275),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_273),u1_struct_0(A_274))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_274),u1_struct_0(B_273),C_275),u1_struct_0(B_273),u1_struct_0(A_274))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_274),u1_struct_0(B_273),C_275))
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | ~ l1_pre_topc(B_273)
      | ~ v2_pre_topc(B_273)
      | ~ v2_funct_1(C_275)
      | k2_relset_1(u1_struct_0(A_274),u1_struct_0(B_273),C_275) != k2_struct_0(B_273)
      | ~ m1_subset_1(D_276,k1_zfmisc_1(u1_struct_0(A_274)))
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_274),u1_struct_0(B_273))))
      | ~ v1_funct_2(C_275,u1_struct_0(A_274),u1_struct_0(B_273))
      | ~ v1_funct_1(C_275)
      | ~ l1_struct_0(B_273)
      | ~ l1_struct_0(A_274) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_30])).

tff(c_1577,plain,(
    ! [D_122] :
      ( r1_tarski(k2_pre_topc('#skF_5',k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_122))),k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_122))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_122),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ v2_funct_1('#skF_6')
      | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_122),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(D_122,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_1541])).

tff(c_1594,plain,(
    ! [D_122] :
      ( r1_tarski(k2_pre_topc('#skF_5',k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_122))),k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_122))))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_122),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(D_122,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_114,c_106,c_66,c_64,c_72,c_70,c_131,c_140,c_1577])).

tff(c_1595,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1594])).

tff(c_1598,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1595])).

tff(c_1602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1598])).

tff(c_1603,plain,(
    ! [D_122] :
      ( ~ l1_struct_0('#skF_5')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
      | r1_tarski(k2_pre_topc('#skF_5',k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_122))),k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k2_pre_topc('#skF_4',k2_pre_topc('#skF_4',D_122))))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',D_122),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(D_122,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1594])).

tff(c_1633,plain,(
    ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1603])).

tff(c_24,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k2_tops_2(A_13,B_14,C_15),k1_zfmisc_1(k2_zfmisc_1(B_14,A_13)))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_2(C_15,A_13,B_14)
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_246,plain,(
    ! [A_163,B_164,C_15] :
      ( m1_subset_1('#skF_1'(A_163,B_164,k2_tops_2(u1_struct_0(B_164),u1_struct_0(A_163),C_15)),k1_zfmisc_1(u1_struct_0(B_164)))
      | v5_pre_topc(k2_tops_2(u1_struct_0(B_164),u1_struct_0(A_163),C_15),A_163,B_164)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_164),u1_struct_0(A_163),C_15),u1_struct_0(A_163),u1_struct_0(B_164))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_164),u1_struct_0(A_163),C_15))
      | ~ l1_pre_topc(B_164)
      | ~ v2_pre_topc(B_164)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_164),u1_struct_0(A_163))))
      | ~ v1_funct_2(C_15,u1_struct_0(B_164),u1_struct_0(A_163))
      | ~ v1_funct_1(C_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_1604,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1594])).

tff(c_32,plain,(
    ! [A_16,B_28,C_34] :
      ( ~ r1_tarski(k2_pre_topc(A_16,k8_relset_1(u1_struct_0(A_16),u1_struct_0(B_28),C_34,'#skF_1'(A_16,B_28,C_34))),k8_relset_1(u1_struct_0(A_16),u1_struct_0(B_28),C_34,k2_pre_topc(B_28,'#skF_1'(A_16,B_28,C_34))))
      | v5_pre_topc(C_34,A_16,B_28)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16),u1_struct_0(B_28))))
      | ~ v1_funct_2(C_34,u1_struct_0(A_16),u1_struct_0(B_28))
      | ~ v1_funct_1(C_34)
      | ~ l1_pre_topc(B_28)
      | ~ v2_pre_topc(B_28)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2206,plain,(
    ! [B_293,A_294,C_295] :
      ( ~ r1_tarski(k2_pre_topc(B_293,k8_relset_1(u1_struct_0(B_293),u1_struct_0(A_294),k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_293),C_295),'#skF_1'(B_293,A_294,k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_293),C_295)))),k7_relset_1(u1_struct_0(A_294),u1_struct_0(B_293),C_295,k2_pre_topc(A_294,'#skF_1'(B_293,A_294,k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_293),C_295)))))
      | v5_pre_topc(k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_293),C_295),B_293,A_294)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_293),C_295),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_293),u1_struct_0(A_294))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_293),C_295),u1_struct_0(B_293),u1_struct_0(A_294))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_293),C_295))
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294)
      | ~ l1_pre_topc(B_293)
      | ~ v2_pre_topc(B_293)
      | ~ v2_funct_1(C_295)
      | k2_relset_1(u1_struct_0(A_294),u1_struct_0(B_293),C_295) != k2_struct_0(B_293)
      | ~ m1_subset_1(k2_pre_topc(A_294,'#skF_1'(B_293,A_294,k2_tops_2(u1_struct_0(A_294),u1_struct_0(B_293),C_295))),k1_zfmisc_1(u1_struct_0(A_294)))
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_294),u1_struct_0(B_293))))
      | ~ v1_funct_2(C_295,u1_struct_0(A_294),u1_struct_0(B_293))
      | ~ v1_funct_1(C_295)
      | ~ l1_struct_0(B_293)
      | ~ l1_struct_0(A_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_32])).

tff(c_2222,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_5',k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))),k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2206])).

tff(c_2225,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_5',k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))),k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_62,c_60,c_58,c_114,c_106,c_66,c_64,c_72,c_70,c_131,c_140,c_2222])).

tff(c_2226,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_5',k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))),k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1633,c_2225])).

tff(c_2227,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_2226])).

tff(c_2230,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_246,c_2227])).

tff(c_2233,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_66,c_64,c_72,c_70,c_131,c_140,c_2230])).

tff(c_2235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1633,c_2233])).

tff(c_2237,plain,(
    m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2226])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k2_pre_topc(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_3)))
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [B_68,A_60,C_72,D_74] :
      ( k8_relset_1(u1_struct_0(B_68),u1_struct_0(A_60),k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),D_74) = k7_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72,D_74)
      | ~ v2_funct_1(C_72)
      | k2_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72) != k2_struct_0(B_68)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_68))))
      | ~ v1_funct_2(C_72,u1_struct_0(A_60),u1_struct_0(B_68))
      | ~ v1_funct_1(C_72)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2236,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ r1_tarski(k2_pre_topc('#skF_5',k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))),k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))))) ),
    inference(splitRight,[status(thm)],[c_2226])).

tff(c_2263,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_5',k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))),k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))))) ),
    inference(splitLeft,[status(thm)],[c_2236])).

tff(c_2266,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))),k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')))))
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2263])).

tff(c_2268,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1604,c_62,c_60,c_58,c_2237,c_114,c_106,c_6,c_2266])).

tff(c_2271,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_2268])).

tff(c_2275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2271])).

tff(c_2276,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2236])).

tff(c_2278,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2276])).

tff(c_2281,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_2278])).

tff(c_2285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2281])).

tff(c_2286,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_2276])).

tff(c_2297,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_2286])).

tff(c_2300,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_2297])).

tff(c_2304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_2300])).

tff(c_2305,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_2286])).

tff(c_2409,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5','#skF_4',k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_2305])).

tff(c_2413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2237,c_2409])).

tff(c_2415,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1603])).

tff(c_12,plain,(
    ! [C_12,A_6,B_10] :
      ( v3_tops_2(C_12,A_6,B_10)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_6),u1_struct_0(B_10),C_12),B_10,A_6)
      | ~ v5_pre_topc(C_12,A_6,B_10)
      | ~ v2_funct_1(C_12)
      | k2_relset_1(u1_struct_0(A_6),u1_struct_0(B_10),C_12) != k2_struct_0(B_10)
      | k1_relset_1(u1_struct_0(A_6),u1_struct_0(B_10),C_12) != k2_struct_0(A_6)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6),u1_struct_0(B_10))))
      | ~ v1_funct_2(C_12,u1_struct_0(A_6),u1_struct_0(B_10))
      | ~ v1_funct_1(C_12)
      | ~ l1_pre_topc(B_10)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2417,plain,
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
    inference(resolution,[status(thm)],[c_2415,c_12])).

tff(c_2420,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_58,c_119,c_114,c_106,c_250,c_2417])).

tff(c_2422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_2420])).

tff(c_2424,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_2425,plain,(
    ! [A_301,B_302,C_303] :
      ( m1_subset_1('#skF_2'(A_301,B_302,C_303),k1_zfmisc_1(u1_struct_0(A_301)))
      | v5_pre_topc(C_303,A_301,B_302)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_301),u1_struct_0(B_302))))
      | ~ v1_funct_2(C_303,u1_struct_0(A_301),u1_struct_0(B_302))
      | ~ v1_funct_1(C_303)
      | ~ l1_pre_topc(B_302)
      | ~ v2_pre_topc(B_302)
      | v2_struct_0(B_302)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2430,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2425])).

tff(c_2434,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_60,c_2430])).

tff(c_2435,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2424,c_2434])).

tff(c_2515,plain,(
    ! [A_332,B_333,C_334] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_332),u1_struct_0(B_333),C_334,k2_pre_topc(A_332,'#skF_2'(A_332,B_333,C_334))),k2_pre_topc(B_333,k7_relset_1(u1_struct_0(A_332),u1_struct_0(B_333),C_334,'#skF_2'(A_332,B_333,C_334))))
      | v5_pre_topc(C_334,A_332,B_333)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_332),u1_struct_0(B_333))))
      | ~ v1_funct_2(C_334,u1_struct_0(A_332),u1_struct_0(B_333))
      | ~ v1_funct_1(C_334)
      | ~ l1_pre_topc(B_333)
      | ~ v2_pre_topc(B_333)
      | v2_struct_0(B_333)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2523,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2515])).

tff(c_2526,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2435,c_72,c_70,c_66,c_64,c_62,c_60,c_58,c_6,c_2523])).

tff(c_2528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2424,c_2526])).

tff(c_2529,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_2530,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_2616,plain,(
    ! [A_362,B_363,C_364] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(A_362),u1_struct_0(B_363),C_364),B_363,A_362)
      | ~ v3_tops_2(C_364,A_362,B_363)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_362),u1_struct_0(B_363))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_362),u1_struct_0(B_363))
      | ~ v1_funct_1(C_364)
      | ~ l1_pre_topc(B_363)
      | v2_struct_0(B_363)
      | ~ l1_pre_topc(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2621,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2616])).

tff(c_2625,plain,
    ( v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_2530,c_2621])).

tff(c_2626,plain,(
    v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2625])).

tff(c_2605,plain,(
    ! [A_356,B_357,C_358] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_356),u1_struct_0(B_357),C_358),B_357,A_356)
      | ~ v3_tops_2(C_358,A_356,B_357)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356),u1_struct_0(B_357))))
      | ~ v1_funct_2(C_358,u1_struct_0(A_356),u1_struct_0(B_357))
      | ~ v1_funct_1(C_358)
      | ~ l1_pre_topc(B_357)
      | ~ l1_pre_topc(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2610,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_2605])).

tff(c_2614,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_2530,c_2610])).

tff(c_2531,plain,(
    ! [A_335,B_336,C_337] :
      ( v1_funct_2(k2_tops_2(A_335,B_336,C_337),B_336,A_335)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(A_335,B_336)))
      | ~ v1_funct_2(C_337,A_335,B_336)
      | ~ v1_funct_1(C_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2533,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_2531])).

tff(c_2536,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2533])).

tff(c_2654,plain,(
    ! [A_375,B_376,C_377,D_378] :
      ( k8_relset_1(u1_struct_0(A_375),u1_struct_0(B_376),C_377,k2_pre_topc(B_376,D_378)) = k2_pre_topc(A_375,k8_relset_1(u1_struct_0(A_375),u1_struct_0(B_376),C_377,D_378))
      | ~ m1_subset_1(D_378,k1_zfmisc_1(u1_struct_0(B_376)))
      | ~ v3_tops_2(C_377,A_375,B_376)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_375),u1_struct_0(B_376))))
      | ~ v1_funct_2(C_377,u1_struct_0(A_375),u1_struct_0(B_376))
      | ~ v1_funct_1(C_377)
      | ~ l1_pre_topc(B_376)
      | ~ v2_pre_topc(B_376)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_2803,plain,(
    ! [A_437,B_438,C_439,D_440] :
      ( k8_relset_1(u1_struct_0(A_437),u1_struct_0(B_438),k2_tops_2(u1_struct_0(B_438),u1_struct_0(A_437),C_439),k2_pre_topc(B_438,D_440)) = k2_pre_topc(A_437,k8_relset_1(u1_struct_0(A_437),u1_struct_0(B_438),k2_tops_2(u1_struct_0(B_438),u1_struct_0(A_437),C_439),D_440))
      | ~ m1_subset_1(D_440,k1_zfmisc_1(u1_struct_0(B_438)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(B_438),u1_struct_0(A_437),C_439),A_437,B_438)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(B_438),u1_struct_0(A_437),C_439),u1_struct_0(A_437),u1_struct_0(B_438))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(B_438),u1_struct_0(A_437),C_439))
      | ~ l1_pre_topc(B_438)
      | ~ v2_pre_topc(B_438)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437)
      | ~ m1_subset_1(C_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_438),u1_struct_0(A_437))))
      | ~ v1_funct_2(C_439,u1_struct_0(B_438),u1_struct_0(A_437))
      | ~ v1_funct_1(C_439) ) ),
    inference(resolution,[status(thm)],[c_24,c_2654])).

tff(c_2884,plain,(
    ! [B_68,A_60,C_72,D_74] :
      ( k8_relset_1(u1_struct_0(B_68),u1_struct_0(A_60),k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),k2_pre_topc(A_60,D_74)) = k2_pre_topc(B_68,k7_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72,D_74))
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),B_68,A_60)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),u1_struct_0(B_68),u1_struct_0(A_60))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | ~ l1_pre_topc(B_68)
      | ~ v2_pre_topc(B_68)
      | v2_struct_0(B_68)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_68))))
      | ~ v1_funct_2(C_72,u1_struct_0(A_60),u1_struct_0(B_68))
      | ~ v1_funct_1(C_72)
      | ~ v2_funct_1(C_72)
      | k2_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72) != k2_struct_0(B_68)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_68))))
      | ~ v1_funct_2(C_72,u1_struct_0(A_60),u1_struct_0(B_68))
      | ~ v1_funct_1(C_72)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_2803])).

tff(c_2678,plain,(
    ! [B_389,A_390,C_391,D_392] :
      ( k8_relset_1(u1_struct_0(B_389),u1_struct_0(A_390),k2_tops_2(u1_struct_0(A_390),u1_struct_0(B_389),C_391),D_392) = k7_relset_1(u1_struct_0(A_390),u1_struct_0(B_389),C_391,D_392)
      | ~ v2_funct_1(C_391)
      | k2_relset_1(u1_struct_0(A_390),u1_struct_0(B_389),C_391) != k2_struct_0(B_389)
      | ~ m1_subset_1(D_392,k1_zfmisc_1(u1_struct_0(A_390)))
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_390),u1_struct_0(B_389))))
      | ~ v1_funct_2(C_391,u1_struct_0(A_390),u1_struct_0(B_389))
      | ~ v1_funct_1(C_391)
      | ~ l1_struct_0(B_389)
      | ~ l1_struct_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2951,plain,(
    ! [B_469,A_470,C_471,D_472] :
      ( r1_tarski(k2_pre_topc(B_469,k7_relset_1(u1_struct_0(A_470),u1_struct_0(B_469),C_471,D_472)),k8_relset_1(u1_struct_0(B_469),u1_struct_0(A_470),k2_tops_2(u1_struct_0(A_470),u1_struct_0(B_469),C_471),k2_pre_topc(A_470,D_472)))
      | ~ m1_subset_1(D_472,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_470),u1_struct_0(B_469),C_471),B_469,A_470)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_470),u1_struct_0(B_469),C_471),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_469),u1_struct_0(A_470))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_470),u1_struct_0(B_469),C_471),u1_struct_0(B_469),u1_struct_0(A_470))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_470),u1_struct_0(B_469),C_471))
      | ~ l1_pre_topc(A_470)
      | ~ v2_pre_topc(A_470)
      | ~ l1_pre_topc(B_469)
      | ~ v2_pre_topc(B_469)
      | ~ v2_funct_1(C_471)
      | k2_relset_1(u1_struct_0(A_470),u1_struct_0(B_469),C_471) != k2_struct_0(B_469)
      | ~ m1_subset_1(D_472,k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_470),u1_struct_0(B_469))))
      | ~ v1_funct_2(C_471,u1_struct_0(A_470),u1_struct_0(B_469))
      | ~ v1_funct_1(C_471)
      | ~ l1_struct_0(B_469)
      | ~ l1_struct_0(A_470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2678,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3163,plain,(
    ! [B_502,A_503,C_504,D_505] :
      ( k8_relset_1(u1_struct_0(B_502),u1_struct_0(A_503),k2_tops_2(u1_struct_0(A_503),u1_struct_0(B_502),C_504),k2_pre_topc(A_503,D_505)) = k2_pre_topc(B_502,k7_relset_1(u1_struct_0(A_503),u1_struct_0(B_502),C_504,D_505))
      | ~ r1_tarski(k8_relset_1(u1_struct_0(B_502),u1_struct_0(A_503),k2_tops_2(u1_struct_0(A_503),u1_struct_0(B_502),C_504),k2_pre_topc(A_503,D_505)),k2_pre_topc(B_502,k7_relset_1(u1_struct_0(A_503),u1_struct_0(B_502),C_504,D_505)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_503),u1_struct_0(B_502),C_504),B_502,A_503)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_503),u1_struct_0(B_502),C_504),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_502),u1_struct_0(A_503))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_503),u1_struct_0(B_502),C_504),u1_struct_0(B_502),u1_struct_0(A_503))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_503),u1_struct_0(B_502),C_504))
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | ~ l1_pre_topc(B_502)
      | ~ v2_pre_topc(B_502)
      | ~ v2_funct_1(C_504)
      | k2_relset_1(u1_struct_0(A_503),u1_struct_0(B_502),C_504) != k2_struct_0(B_502)
      | ~ m1_subset_1(D_505,k1_zfmisc_1(u1_struct_0(A_503)))
      | ~ m1_subset_1(C_504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_503),u1_struct_0(B_502))))
      | ~ v1_funct_2(C_504,u1_struct_0(A_503),u1_struct_0(B_502))
      | ~ v1_funct_1(C_504)
      | ~ l1_struct_0(B_502)
      | ~ l1_struct_0(A_503) ) ),
    inference(resolution,[status(thm)],[c_2951,c_2])).

tff(c_3169,plain,(
    ! [B_68,A_60,C_72,D_74] :
      ( k8_relset_1(u1_struct_0(B_68),u1_struct_0(A_60),k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),k2_pre_topc(A_60,D_74)) = k2_pre_topc(B_68,k7_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72,D_74))
      | ~ r1_tarski(k2_pre_topc(B_68,k7_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72,D_74)),k2_pre_topc(B_68,k7_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72,D_74)))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),B_68,A_60)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_68),u1_struct_0(A_60))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),u1_struct_0(B_68),u1_struct_0(A_60))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | ~ l1_pre_topc(B_68)
      | ~ v2_pre_topc(B_68)
      | ~ v2_funct_1(C_72)
      | k2_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72) != k2_struct_0(B_68)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_68))))
      | ~ v1_funct_2(C_72,u1_struct_0(A_60),u1_struct_0(B_68))
      | ~ v1_funct_1(C_72)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_60)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),B_68,A_60)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72),u1_struct_0(B_68),u1_struct_0(A_60))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_60),u1_struct_0(B_68),C_72))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | ~ l1_pre_topc(B_68)
      | ~ v2_pre_topc(B_68)
      | v2_struct_0(B_68)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_68))))
      | ~ v1_funct_2(C_72,u1_struct_0(A_60),u1_struct_0(B_68))
      | ~ v1_funct_1(C_72)
      | ~ v2_funct_1(C_72)
      | k2_relset_1(u1_struct_0(A_60),u1_struct_0(B_68),C_72) != k2_struct_0(B_68)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_68))))
      | ~ v1_funct_2(C_72,u1_struct_0(A_60),u1_struct_0(B_68))
      | ~ v1_funct_1(C_72)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2884,c_3163])).

tff(c_3182,plain,(
    ! [B_506,A_507,C_508,D_509] :
      ( k8_relset_1(u1_struct_0(B_506),u1_struct_0(A_507),k2_tops_2(u1_struct_0(A_507),u1_struct_0(B_506),C_508),k2_pre_topc(A_507,D_509)) = k2_pre_topc(B_506,k7_relset_1(u1_struct_0(A_507),u1_struct_0(B_506),C_508,D_509))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_507),u1_struct_0(B_506),C_508),B_506,A_507)
      | ~ m1_subset_1(k2_tops_2(u1_struct_0(A_507),u1_struct_0(B_506),C_508),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_506),u1_struct_0(A_507))))
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_507),u1_struct_0(B_506),C_508),B_506,A_507)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_507),u1_struct_0(B_506),C_508),u1_struct_0(B_506),u1_struct_0(A_507))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_507),u1_struct_0(B_506),C_508))
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | ~ l1_pre_topc(B_506)
      | ~ v2_pre_topc(B_506)
      | v2_struct_0(B_506)
      | ~ v2_funct_1(C_508)
      | k2_relset_1(u1_struct_0(A_507),u1_struct_0(B_506),C_508) != k2_struct_0(B_506)
      | ~ m1_subset_1(D_509,k1_zfmisc_1(u1_struct_0(A_507)))
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_507),u1_struct_0(B_506))))
      | ~ v1_funct_2(C_508,u1_struct_0(A_507),u1_struct_0(B_506))
      | ~ v1_funct_1(C_508)
      | ~ l1_struct_0(B_506)
      | ~ l1_struct_0(A_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3169])).

tff(c_3187,plain,(
    ! [B_510,A_511,C_512,D_513] :
      ( k8_relset_1(u1_struct_0(B_510),u1_struct_0(A_511),k2_tops_2(u1_struct_0(A_511),u1_struct_0(B_510),C_512),k2_pre_topc(A_511,D_513)) = k2_pre_topc(B_510,k7_relset_1(u1_struct_0(A_511),u1_struct_0(B_510),C_512,D_513))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_511),u1_struct_0(B_510),C_512),B_510,A_511)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_511),u1_struct_0(B_510),C_512),B_510,A_511)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_511),u1_struct_0(B_510),C_512),u1_struct_0(B_510),u1_struct_0(A_511))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_511),u1_struct_0(B_510),C_512))
      | ~ l1_pre_topc(A_511)
      | ~ v2_pre_topc(A_511)
      | ~ l1_pre_topc(B_510)
      | ~ v2_pre_topc(B_510)
      | v2_struct_0(B_510)
      | ~ v2_funct_1(C_512)
      | k2_relset_1(u1_struct_0(A_511),u1_struct_0(B_510),C_512) != k2_struct_0(B_510)
      | ~ m1_subset_1(D_513,k1_zfmisc_1(u1_struct_0(A_511)))
      | ~ l1_struct_0(B_510)
      | ~ l1_struct_0(A_511)
      | ~ m1_subset_1(C_512,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_511),u1_struct_0(B_510))))
      | ~ v1_funct_2(C_512,u1_struct_0(A_511),u1_struct_0(B_510))
      | ~ v1_funct_1(C_512) ) ),
    inference(resolution,[status(thm)],[c_24,c_3182])).

tff(c_3325,plain,(
    ! [A_524,B_525,C_526,D_527] :
      ( k7_relset_1(u1_struct_0(A_524),u1_struct_0(B_525),C_526,k2_pre_topc(A_524,D_527)) = k2_pre_topc(B_525,k7_relset_1(u1_struct_0(A_524),u1_struct_0(B_525),C_526,D_527))
      | ~ v2_funct_1(C_526)
      | k2_relset_1(u1_struct_0(A_524),u1_struct_0(B_525),C_526) != k2_struct_0(B_525)
      | ~ m1_subset_1(k2_pre_topc(A_524,D_527),k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_524),u1_struct_0(B_525))))
      | ~ v1_funct_2(C_526,u1_struct_0(A_524),u1_struct_0(B_525))
      | ~ v1_funct_1(C_526)
      | ~ l1_struct_0(B_525)
      | ~ l1_struct_0(A_524)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_524),u1_struct_0(B_525),C_526),B_525,A_524)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_524),u1_struct_0(B_525),C_526),B_525,A_524)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_524),u1_struct_0(B_525),C_526),u1_struct_0(B_525),u1_struct_0(A_524))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_524),u1_struct_0(B_525),C_526))
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | ~ l1_pre_topc(B_525)
      | ~ v2_pre_topc(B_525)
      | v2_struct_0(B_525)
      | ~ v2_funct_1(C_526)
      | k2_relset_1(u1_struct_0(A_524),u1_struct_0(B_525),C_526) != k2_struct_0(B_525)
      | ~ m1_subset_1(D_527,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ l1_struct_0(B_525)
      | ~ l1_struct_0(A_524)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_524),u1_struct_0(B_525))))
      | ~ v1_funct_2(C_526,u1_struct_0(A_524),u1_struct_0(B_525))
      | ~ v1_funct_1(C_526) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3187,c_42])).

tff(c_3333,plain,(
    ! [A_528,B_529,C_530,B_531] :
      ( k7_relset_1(u1_struct_0(A_528),u1_struct_0(B_529),C_530,k2_pre_topc(A_528,B_531)) = k2_pre_topc(B_529,k7_relset_1(u1_struct_0(A_528),u1_struct_0(B_529),C_530,B_531))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_528),u1_struct_0(B_529),C_530),B_529,A_528)
      | ~ v3_tops_2(k2_tops_2(u1_struct_0(A_528),u1_struct_0(B_529),C_530),B_529,A_528)
      | ~ v1_funct_2(k2_tops_2(u1_struct_0(A_528),u1_struct_0(B_529),C_530),u1_struct_0(B_529),u1_struct_0(A_528))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0(A_528),u1_struct_0(B_529),C_530))
      | ~ v2_pre_topc(A_528)
      | ~ l1_pre_topc(B_529)
      | ~ v2_pre_topc(B_529)
      | v2_struct_0(B_529)
      | ~ v2_funct_1(C_530)
      | k2_relset_1(u1_struct_0(A_528),u1_struct_0(B_529),C_530) != k2_struct_0(B_529)
      | ~ l1_struct_0(B_529)
      | ~ l1_struct_0(A_528)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_528),u1_struct_0(B_529))))
      | ~ v1_funct_2(C_530,u1_struct_0(A_528),u1_struct_0(B_529))
      | ~ v1_funct_1(C_530)
      | ~ m1_subset_1(B_531,k1_zfmisc_1(u1_struct_0(A_528)))
      | ~ l1_pre_topc(A_528) ) ),
    inference(resolution,[status(thm)],[c_8,c_3325])).

tff(c_3338,plain,(
    ! [B_531] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',B_531)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',B_531))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
      | ~ v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'),'#skF_5','#skF_4')
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6'))
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v2_funct_1('#skF_6')
      | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(B_531,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2536,c_3333])).

tff(c_3342,plain,(
    ! [B_531] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',B_531)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',B_531))
      | v2_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(B_531,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_62,c_60,c_58,c_114,c_106,c_66,c_64,c_72,c_131,c_2626,c_2614,c_3338])).

tff(c_3343,plain,(
    ! [B_531] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',B_531)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',B_531))
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ m1_subset_1(B_531,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3342])).

tff(c_3344,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3343])).

tff(c_3347,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_3344])).

tff(c_3351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3347])).

tff(c_3352,plain,(
    ! [B_531] :
      ( ~ l1_struct_0('#skF_5')
      | k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',B_531)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',B_531))
      | ~ m1_subset_1(B_531,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_3343])).

tff(c_3354,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3352])).

tff(c_3357,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_3354])).

tff(c_3361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3357])).

tff(c_3364,plain,(
    ! [B_532] :
      ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4',B_532)) = k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',B_532))
      | ~ m1_subset_1(B_532,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_3352])).

tff(c_76,plain,
    ( k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4','#skF_7')) != k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7'))
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5')
    | k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_2571,plain,(
    k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_pre_topc('#skF_4','#skF_7')) != k2_pre_topc('#skF_5',k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2530,c_119,c_114,c_106,c_76])).

tff(c_3399,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3364,c_2571])).

tff(c_3434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2529,c_3399])).

tff(c_3436,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_3435,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_3486,plain,(
    ! [A_550,B_551,C_552] :
      ( k1_relset_1(u1_struct_0(A_550),u1_struct_0(B_551),C_552) = k2_struct_0(A_550)
      | ~ v3_tops_2(C_552,A_550,B_551)
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_550),u1_struct_0(B_551))))
      | ~ v1_funct_2(C_552,u1_struct_0(A_550),u1_struct_0(B_551))
      | ~ v1_funct_1(C_552)
      | ~ l1_pre_topc(B_551)
      | ~ l1_pre_topc(A_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3493,plain,
    ( k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3486])).

tff(c_3497,plain,(
    k1_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_3435,c_3493])).

tff(c_3499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3436,c_3497])).

tff(c_3501,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') != k2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_3500,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_3556,plain,(
    ! [A_570,B_571,C_572] :
      ( k2_relset_1(u1_struct_0(A_570),u1_struct_0(B_571),C_572) = k2_struct_0(B_571)
      | ~ v3_tops_2(C_572,A_570,B_571)
      | ~ m1_subset_1(C_572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_570),u1_struct_0(B_571))))
      | ~ v1_funct_2(C_572,u1_struct_0(A_570),u1_struct_0(B_571))
      | ~ v1_funct_1(C_572)
      | ~ l1_pre_topc(B_571)
      | ~ l1_pre_topc(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3563,plain,
    ( k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3556])).

tff(c_3567,plain,(
    k2_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6') = k2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_3500,c_3563])).

tff(c_3569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3501,c_3567])).

tff(c_3571,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_3570,plain,(
    v3_tops_2('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_3603,plain,(
    ! [C_586,A_587,B_588] :
      ( v2_funct_1(C_586)
      | ~ v3_tops_2(C_586,A_587,B_588)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_587),u1_struct_0(B_588))))
      | ~ v1_funct_2(C_586,u1_struct_0(A_587),u1_struct_0(B_588))
      | ~ v1_funct_1(C_586)
      | ~ l1_pre_topc(B_588)
      | ~ l1_pre_topc(A_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3610,plain,
    ( v2_funct_1('#skF_6')
    | ~ v3_tops_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_3603])).

tff(c_3614,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_62,c_60,c_3570,c_3610])).

tff(c_3616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3571,c_3614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:48:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.82/2.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/2.77  
% 7.82/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/2.78  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 7.82/2.78  
% 7.82/2.78  %Foreground sorts:
% 7.82/2.78  
% 7.82/2.78  
% 7.82/2.78  %Background operators:
% 7.82/2.78  
% 7.82/2.78  
% 7.82/2.78  %Foreground operators:
% 7.82/2.78  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.82/2.78  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.82/2.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.82/2.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.82/2.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.82/2.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.82/2.78  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.82/2.78  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 7.82/2.78  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.82/2.78  tff('#skF_7', type, '#skF_7': $i).
% 7.82/2.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.82/2.78  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 7.82/2.78  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.82/2.78  tff('#skF_5', type, '#skF_5': $i).
% 7.82/2.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.82/2.78  tff('#skF_6', type, '#skF_6': $i).
% 7.82/2.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.82/2.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.82/2.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.82/2.78  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.82/2.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.82/2.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.82/2.78  tff('#skF_4', type, '#skF_4': $i).
% 7.82/2.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.82/2.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.82/2.78  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.82/2.78  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.82/2.78  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.82/2.78  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.82/2.78  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.82/2.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.82/2.78  
% 8.13/2.83  tff(f_231, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> ((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(A, D)) = k2_pre_topc(B, k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_2)).
% 8.13/2.83  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => r1_tarski(k2_pre_topc(A, k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D)), k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(B, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tops_2)).
% 8.13/2.83  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.13/2.83  tff(f_77, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 8.13/2.83  tff(f_147, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => (k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k8_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tops_2)).
% 8.13/2.83  tff(f_37, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 8.13/2.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.13/2.83  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> (((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) & v5_pre_topc(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 8.13/2.83  tff(f_126, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(A, D)), k2_pre_topc(B, k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_tops_2)).
% 8.13/2.83  tff(f_166, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) => v3_tops_2(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C), B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_tops_2)).
% 8.13/2.83  tff(f_198, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> ((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_pre_topc(B, D)) = k2_pre_topc(A, k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_tops_2)).
% 8.13/2.83  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_98, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_119, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_98])).
% 8.13/2.83  tff(c_92, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_114, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_92])).
% 8.13/2.83  tff(c_86, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_106, plain, (v2_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_86])).
% 8.13/2.83  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_133, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_114, c_106, c_78])).
% 8.13/2.83  tff(c_134, plain, (~v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_133])).
% 8.13/2.83  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_64, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_60, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_72, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_66, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_240, plain, (![A_163, B_164, C_165]: (m1_subset_1('#skF_1'(A_163, B_164, C_165), k1_zfmisc_1(u1_struct_0(B_164))) | v5_pre_topc(C_165, A_163, B_164) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_163), u1_struct_0(B_164)))) | ~v1_funct_2(C_165, u1_struct_0(A_163), u1_struct_0(B_164)) | ~v1_funct_1(C_165) | ~l1_pre_topc(B_164) | ~v2_pre_topc(B_164) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.13/2.83  tff(c_245, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_240])).
% 8.13/2.83  tff(c_249, plain, (m1_subset_1('#skF_1'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_245])).
% 8.13/2.83  tff(c_250, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_249])).
% 8.13/2.83  tff(c_10, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.13/2.83  tff(c_125, plain, (![A_129, B_130, C_131]: (v1_funct_1(k2_tops_2(A_129, B_130, C_131)) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_2(C_131, A_129, B_130) | ~v1_funct_1(C_131))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.13/2.83  tff(c_128, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_125])).
% 8.13/2.83  tff(c_131, plain, (v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_128])).
% 8.13/2.83  tff(c_135, plain, (![A_132, B_133, C_134]: (v1_funct_2(k2_tops_2(A_132, B_133, C_134), B_133, A_132) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_2(C_134, A_132, B_133) | ~v1_funct_1(C_134))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.13/2.83  tff(c_137, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_135])).
% 8.13/2.83  tff(c_140, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_137])).
% 8.13/2.83  tff(c_80, plain, (![D_122]: (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', D_122))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_122)) | ~m1_subset_1(D_122, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_161, plain, (![D_122]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', D_122))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_122)) | ~m1_subset_1(D_122, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_134, c_80])).
% 8.13/2.83  tff(c_285, plain, (![B_183, A_184, C_185, D_186]: (k8_relset_1(u1_struct_0(B_183), u1_struct_0(A_184), k2_tops_2(u1_struct_0(A_184), u1_struct_0(B_183), C_185), D_186)=k7_relset_1(u1_struct_0(A_184), u1_struct_0(B_183), C_185, D_186) | ~v2_funct_1(C_185) | k2_relset_1(u1_struct_0(A_184), u1_struct_0(B_183), C_185)!=k2_struct_0(B_183) | ~m1_subset_1(D_186, k1_zfmisc_1(u1_struct_0(A_184))) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_184), u1_struct_0(B_183)))) | ~v1_funct_2(C_185, u1_struct_0(A_184), u1_struct_0(B_183)) | ~v1_funct_1(C_185) | ~l1_struct_0(B_183) | ~l1_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.13/2.83  tff(c_30, plain, (![A_16, B_28, C_34, D_37]: (r1_tarski(k2_pre_topc(A_16, k8_relset_1(u1_struct_0(A_16), u1_struct_0(B_28), C_34, D_37)), k8_relset_1(u1_struct_0(A_16), u1_struct_0(B_28), C_34, k2_pre_topc(B_28, D_37))) | ~m1_subset_1(D_37, k1_zfmisc_1(u1_struct_0(B_28))) | ~v5_pre_topc(C_34, A_16, B_28) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16), u1_struct_0(B_28)))) | ~v1_funct_2(C_34, u1_struct_0(A_16), u1_struct_0(B_28)) | ~v1_funct_1(C_34) | ~l1_pre_topc(B_28) | ~v2_pre_topc(B_28) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.13/2.83  tff(c_1541, plain, (![B_273, A_274, C_275, D_276]: (r1_tarski(k2_pre_topc(B_273, k7_relset_1(u1_struct_0(A_274), u1_struct_0(B_273), C_275, D_276)), k8_relset_1(u1_struct_0(B_273), u1_struct_0(A_274), k2_tops_2(u1_struct_0(A_274), u1_struct_0(B_273), C_275), k2_pre_topc(A_274, D_276))) | ~m1_subset_1(D_276, k1_zfmisc_1(u1_struct_0(A_274))) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_274), u1_struct_0(B_273), C_275), B_273, A_274) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_274), u1_struct_0(B_273), C_275), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_273), u1_struct_0(A_274)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_274), u1_struct_0(B_273), C_275), u1_struct_0(B_273), u1_struct_0(A_274)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_274), u1_struct_0(B_273), C_275)) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | ~l1_pre_topc(B_273) | ~v2_pre_topc(B_273) | ~v2_funct_1(C_275) | k2_relset_1(u1_struct_0(A_274), u1_struct_0(B_273), C_275)!=k2_struct_0(B_273) | ~m1_subset_1(D_276, k1_zfmisc_1(u1_struct_0(A_274))) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_274), u1_struct_0(B_273)))) | ~v1_funct_2(C_275, u1_struct_0(A_274), u1_struct_0(B_273)) | ~v1_funct_1(C_275) | ~l1_struct_0(B_273) | ~l1_struct_0(A_274))), inference(superposition, [status(thm), theory('equality')], [c_285, c_30])).
% 8.13/2.83  tff(c_1577, plain, (![D_122]: (r1_tarski(k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_122))), k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k2_pre_topc('#skF_4', k2_pre_topc('#skF_4', D_122)))) | ~m1_subset_1(k2_pre_topc('#skF_4', D_122), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | ~m1_subset_1(k2_pre_topc('#skF_4', D_122), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | ~m1_subset_1(D_122, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_161, c_1541])).
% 8.13/2.83  tff(c_1594, plain, (![D_122]: (r1_tarski(k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_122))), k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k2_pre_topc('#skF_4', k2_pre_topc('#skF_4', D_122)))) | ~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~m1_subset_1(k2_pre_topc('#skF_4', D_122), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | ~m1_subset_1(D_122, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_114, c_106, c_66, c_64, c_72, c_70, c_131, c_140, c_1577])).
% 8.13/2.83  tff(c_1595, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1594])).
% 8.13/2.83  tff(c_1598, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_1595])).
% 8.13/2.83  tff(c_1602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1598])).
% 8.13/2.83  tff(c_1603, plain, (![D_122]: (~l1_struct_0('#skF_5') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | r1_tarski(k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', D_122))), k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k2_pre_topc('#skF_4', k2_pre_topc('#skF_4', D_122)))) | ~m1_subset_1(k2_pre_topc('#skF_4', D_122), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(D_122, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1594])).
% 8.13/2.83  tff(c_1633, plain, (~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1603])).
% 8.13/2.83  tff(c_24, plain, (![A_13, B_14, C_15]: (m1_subset_1(k2_tops_2(A_13, B_14, C_15), k1_zfmisc_1(k2_zfmisc_1(B_14, A_13))) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_2(C_15, A_13, B_14) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.13/2.83  tff(c_246, plain, (![A_163, B_164, C_15]: (m1_subset_1('#skF_1'(A_163, B_164, k2_tops_2(u1_struct_0(B_164), u1_struct_0(A_163), C_15)), k1_zfmisc_1(u1_struct_0(B_164))) | v5_pre_topc(k2_tops_2(u1_struct_0(B_164), u1_struct_0(A_163), C_15), A_163, B_164) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_164), u1_struct_0(A_163), C_15), u1_struct_0(A_163), u1_struct_0(B_164)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_164), u1_struct_0(A_163), C_15)) | ~l1_pre_topc(B_164) | ~v2_pre_topc(B_164) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_164), u1_struct_0(A_163)))) | ~v1_funct_2(C_15, u1_struct_0(B_164), u1_struct_0(A_163)) | ~v1_funct_1(C_15))), inference(resolution, [status(thm)], [c_24, c_240])).
% 8.13/2.83  tff(c_1604, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1594])).
% 8.13/2.83  tff(c_32, plain, (![A_16, B_28, C_34]: (~r1_tarski(k2_pre_topc(A_16, k8_relset_1(u1_struct_0(A_16), u1_struct_0(B_28), C_34, '#skF_1'(A_16, B_28, C_34))), k8_relset_1(u1_struct_0(A_16), u1_struct_0(B_28), C_34, k2_pre_topc(B_28, '#skF_1'(A_16, B_28, C_34)))) | v5_pre_topc(C_34, A_16, B_28) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_16), u1_struct_0(B_28)))) | ~v1_funct_2(C_34, u1_struct_0(A_16), u1_struct_0(B_28)) | ~v1_funct_1(C_34) | ~l1_pre_topc(B_28) | ~v2_pre_topc(B_28) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.13/2.83  tff(c_2206, plain, (![B_293, A_294, C_295]: (~r1_tarski(k2_pre_topc(B_293, k8_relset_1(u1_struct_0(B_293), u1_struct_0(A_294), k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_293), C_295), '#skF_1'(B_293, A_294, k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_293), C_295)))), k7_relset_1(u1_struct_0(A_294), u1_struct_0(B_293), C_295, k2_pre_topc(A_294, '#skF_1'(B_293, A_294, k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_293), C_295))))) | v5_pre_topc(k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_293), C_295), B_293, A_294) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_293), C_295), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_293), u1_struct_0(A_294)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_293), C_295), u1_struct_0(B_293), u1_struct_0(A_294)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_293), C_295)) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294) | ~l1_pre_topc(B_293) | ~v2_pre_topc(B_293) | ~v2_funct_1(C_295) | k2_relset_1(u1_struct_0(A_294), u1_struct_0(B_293), C_295)!=k2_struct_0(B_293) | ~m1_subset_1(k2_pre_topc(A_294, '#skF_1'(B_293, A_294, k2_tops_2(u1_struct_0(A_294), u1_struct_0(B_293), C_295))), k1_zfmisc_1(u1_struct_0(A_294))) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_294), u1_struct_0(B_293)))) | ~v1_funct_2(C_295, u1_struct_0(A_294), u1_struct_0(B_293)) | ~v1_funct_1(C_295) | ~l1_struct_0(B_293) | ~l1_struct_0(A_294))), inference(superposition, [status(thm), theory('equality')], [c_285, c_32])).
% 8.13/2.83  tff(c_2222, plain, (~r1_tarski(k2_pre_topc('#skF_5', k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))) | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | ~m1_subset_1(k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_161, c_2206])).
% 8.13/2.83  tff(c_2225, plain, (~r1_tarski(k2_pre_topc('#skF_5', k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))) | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~m1_subset_1(k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1604, c_62, c_60, c_58, c_114, c_106, c_66, c_64, c_72, c_70, c_131, c_140, c_2222])).
% 8.13/2.83  tff(c_2226, plain, (~r1_tarski(k2_pre_topc('#skF_5', k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~m1_subset_1(k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_5') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1633, c_2225])).
% 8.13/2.83  tff(c_2227, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_2226])).
% 8.13/2.83  tff(c_2230, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_246, c_2227])).
% 8.13/2.83  tff(c_2233, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_66, c_64, c_72, c_70, c_131, c_140, c_2230])).
% 8.13/2.83  tff(c_2235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1633, c_2233])).
% 8.13/2.83  tff(c_2237, plain, (m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2226])).
% 8.13/2.83  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k2_pre_topc(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_3))) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.13/2.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.13/2.83  tff(c_42, plain, (![B_68, A_60, C_72, D_74]: (k8_relset_1(u1_struct_0(B_68), u1_struct_0(A_60), k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), D_74)=k7_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72, D_74) | ~v2_funct_1(C_72) | k2_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72)!=k2_struct_0(B_68) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60), u1_struct_0(B_68)))) | ~v1_funct_2(C_72, u1_struct_0(A_60), u1_struct_0(B_68)) | ~v1_funct_1(C_72) | ~l1_struct_0(B_68) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.13/2.83  tff(c_2236, plain, (~l1_struct_0('#skF_5') | ~m1_subset_1(k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~r1_tarski(k2_pre_topc('#skF_5', k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))))), inference(splitRight, [status(thm)], [c_2226])).
% 8.13/2.83  tff(c_2263, plain, (~r1_tarski(k2_pre_topc('#skF_5', k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'), k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))))), inference(splitLeft, [status(thm)], [c_2236])).
% 8.13/2.83  tff(c_2266, plain, (~r1_tarski(k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')))), k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))))) | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_42, c_2263])).
% 8.13/2.83  tff(c_2268, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1604, c_62, c_60, c_58, c_2237, c_114, c_106, c_6, c_2266])).
% 8.13/2.83  tff(c_2271, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_10, c_2268])).
% 8.13/2.83  tff(c_2275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_2271])).
% 8.13/2.83  tff(c_2276, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4')))) | ~m1_subset_1(k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_2236])).
% 8.13/2.83  tff(c_2278, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_2276])).
% 8.13/2.83  tff(c_2281, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_10, c_2278])).
% 8.13/2.83  tff(c_2285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_2281])).
% 8.13/2.83  tff(c_2286, plain, (~m1_subset_1(k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_2276])).
% 8.13/2.83  tff(c_2297, plain, (~m1_subset_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_2286])).
% 8.13/2.83  tff(c_2300, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_2297])).
% 8.13/2.83  tff(c_2304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_2300])).
% 8.13/2.83  tff(c_2305, plain, (~m1_subset_1(k2_pre_topc('#skF_4', '#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'))), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_2286])).
% 8.13/2.83  tff(c_2409, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_4', k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_2305])).
% 8.13/2.83  tff(c_2413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_2237, c_2409])).
% 8.13/2.83  tff(c_2415, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1603])).
% 8.13/2.83  tff(c_12, plain, (![C_12, A_6, B_10]: (v3_tops_2(C_12, A_6, B_10) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_6), u1_struct_0(B_10), C_12), B_10, A_6) | ~v5_pre_topc(C_12, A_6, B_10) | ~v2_funct_1(C_12) | k2_relset_1(u1_struct_0(A_6), u1_struct_0(B_10), C_12)!=k2_struct_0(B_10) | k1_relset_1(u1_struct_0(A_6), u1_struct_0(B_10), C_12)!=k2_struct_0(A_6) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6), u1_struct_0(B_10)))) | ~v1_funct_2(C_12, u1_struct_0(A_6), u1_struct_0(B_10)) | ~v1_funct_1(C_12) | ~l1_pre_topc(B_10) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.13/2.83  tff(c_2417, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2415, c_12])).
% 8.13/2.83  tff(c_2420, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_58, c_119, c_114, c_106, c_250, c_2417])).
% 8.13/2.83  tff(c_2422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_2420])).
% 8.13/2.83  tff(c_2424, plain, (~v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_249])).
% 8.13/2.83  tff(c_2425, plain, (![A_301, B_302, C_303]: (m1_subset_1('#skF_2'(A_301, B_302, C_303), k1_zfmisc_1(u1_struct_0(A_301))) | v5_pre_topc(C_303, A_301, B_302) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_301), u1_struct_0(B_302)))) | ~v1_funct_2(C_303, u1_struct_0(A_301), u1_struct_0(B_302)) | ~v1_funct_1(C_303) | ~l1_pre_topc(B_302) | ~v2_pre_topc(B_302) | v2_struct_0(B_302) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.13/2.83  tff(c_2430, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2425])).
% 8.13/2.83  tff(c_2434, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_60, c_2430])).
% 8.13/2.83  tff(c_2435, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_2424, c_2434])).
% 8.13/2.83  tff(c_2515, plain, (![A_332, B_333, C_334]: (~r1_tarski(k7_relset_1(u1_struct_0(A_332), u1_struct_0(B_333), C_334, k2_pre_topc(A_332, '#skF_2'(A_332, B_333, C_334))), k2_pre_topc(B_333, k7_relset_1(u1_struct_0(A_332), u1_struct_0(B_333), C_334, '#skF_2'(A_332, B_333, C_334)))) | v5_pre_topc(C_334, A_332, B_333) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_332), u1_struct_0(B_333)))) | ~v1_funct_2(C_334, u1_struct_0(A_332), u1_struct_0(B_333)) | ~v1_funct_1(C_334) | ~l1_pre_topc(B_333) | ~v2_pre_topc(B_333) | v2_struct_0(B_333) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332))), inference(cnfTransformation, [status(thm)], [f_126])).
% 8.13/2.83  tff(c_2523, plain, (~r1_tarski(k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_6'))), k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_2'('#skF_4', '#skF_5', '#skF_6')))) | v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_161, c_2515])).
% 8.13/2.83  tff(c_2526, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2435, c_72, c_70, c_66, c_64, c_62, c_60, c_58, c_6, c_2523])).
% 8.13/2.83  tff(c_2528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2424, c_2526])).
% 8.13/2.83  tff(c_2529, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_133])).
% 8.13/2.83  tff(c_2530, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_133])).
% 8.13/2.83  tff(c_2616, plain, (![A_362, B_363, C_364]: (v3_tops_2(k2_tops_2(u1_struct_0(A_362), u1_struct_0(B_363), C_364), B_363, A_362) | ~v3_tops_2(C_364, A_362, B_363) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_362), u1_struct_0(B_363)))) | ~v1_funct_2(C_364, u1_struct_0(A_362), u1_struct_0(B_363)) | ~v1_funct_1(C_364) | ~l1_pre_topc(B_363) | v2_struct_0(B_363) | ~l1_pre_topc(A_362))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.13/2.83  tff(c_2621, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2616])).
% 8.13/2.83  tff(c_2625, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_2530, c_2621])).
% 8.13/2.83  tff(c_2626, plain, (v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_2625])).
% 8.13/2.83  tff(c_2605, plain, (![A_356, B_357, C_358]: (v5_pre_topc(k2_tops_2(u1_struct_0(A_356), u1_struct_0(B_357), C_358), B_357, A_356) | ~v3_tops_2(C_358, A_356, B_357) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356), u1_struct_0(B_357)))) | ~v1_funct_2(C_358, u1_struct_0(A_356), u1_struct_0(B_357)) | ~v1_funct_1(C_358) | ~l1_pre_topc(B_357) | ~l1_pre_topc(A_356))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.13/2.83  tff(c_2610, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_2605])).
% 8.13/2.83  tff(c_2614, plain, (v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_2530, c_2610])).
% 8.13/2.83  tff(c_2531, plain, (![A_335, B_336, C_337]: (v1_funct_2(k2_tops_2(A_335, B_336, C_337), B_336, A_335) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(A_335, B_336))) | ~v1_funct_2(C_337, A_335, B_336) | ~v1_funct_1(C_337))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.13/2.83  tff(c_2533, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_2531])).
% 8.13/2.83  tff(c_2536, plain, (v1_funct_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2533])).
% 8.13/2.83  tff(c_2654, plain, (![A_375, B_376, C_377, D_378]: (k8_relset_1(u1_struct_0(A_375), u1_struct_0(B_376), C_377, k2_pre_topc(B_376, D_378))=k2_pre_topc(A_375, k8_relset_1(u1_struct_0(A_375), u1_struct_0(B_376), C_377, D_378)) | ~m1_subset_1(D_378, k1_zfmisc_1(u1_struct_0(B_376))) | ~v3_tops_2(C_377, A_375, B_376) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_375), u1_struct_0(B_376)))) | ~v1_funct_2(C_377, u1_struct_0(A_375), u1_struct_0(B_376)) | ~v1_funct_1(C_377) | ~l1_pre_topc(B_376) | ~v2_pre_topc(B_376) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(cnfTransformation, [status(thm)], [f_198])).
% 8.13/2.83  tff(c_2803, plain, (![A_437, B_438, C_439, D_440]: (k8_relset_1(u1_struct_0(A_437), u1_struct_0(B_438), k2_tops_2(u1_struct_0(B_438), u1_struct_0(A_437), C_439), k2_pre_topc(B_438, D_440))=k2_pre_topc(A_437, k8_relset_1(u1_struct_0(A_437), u1_struct_0(B_438), k2_tops_2(u1_struct_0(B_438), u1_struct_0(A_437), C_439), D_440)) | ~m1_subset_1(D_440, k1_zfmisc_1(u1_struct_0(B_438))) | ~v3_tops_2(k2_tops_2(u1_struct_0(B_438), u1_struct_0(A_437), C_439), A_437, B_438) | ~v1_funct_2(k2_tops_2(u1_struct_0(B_438), u1_struct_0(A_437), C_439), u1_struct_0(A_437), u1_struct_0(B_438)) | ~v1_funct_1(k2_tops_2(u1_struct_0(B_438), u1_struct_0(A_437), C_439)) | ~l1_pre_topc(B_438) | ~v2_pre_topc(B_438) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437) | ~m1_subset_1(C_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_438), u1_struct_0(A_437)))) | ~v1_funct_2(C_439, u1_struct_0(B_438), u1_struct_0(A_437)) | ~v1_funct_1(C_439))), inference(resolution, [status(thm)], [c_24, c_2654])).
% 8.13/2.83  tff(c_2884, plain, (![B_68, A_60, C_72, D_74]: (k8_relset_1(u1_struct_0(B_68), u1_struct_0(A_60), k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), k2_pre_topc(A_60, D_74))=k2_pre_topc(B_68, k7_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72, D_74)) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_60))) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), B_68, A_60) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), u1_struct_0(B_68), u1_struct_0(A_60)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | ~l1_pre_topc(B_68) | ~v2_pre_topc(B_68) | v2_struct_0(B_68) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60), u1_struct_0(B_68)))) | ~v1_funct_2(C_72, u1_struct_0(A_60), u1_struct_0(B_68)) | ~v1_funct_1(C_72) | ~v2_funct_1(C_72) | k2_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72)!=k2_struct_0(B_68) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60), u1_struct_0(B_68)))) | ~v1_funct_2(C_72, u1_struct_0(A_60), u1_struct_0(B_68)) | ~v1_funct_1(C_72) | ~l1_struct_0(B_68) | ~l1_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_42, c_2803])).
% 8.13/2.83  tff(c_2678, plain, (![B_389, A_390, C_391, D_392]: (k8_relset_1(u1_struct_0(B_389), u1_struct_0(A_390), k2_tops_2(u1_struct_0(A_390), u1_struct_0(B_389), C_391), D_392)=k7_relset_1(u1_struct_0(A_390), u1_struct_0(B_389), C_391, D_392) | ~v2_funct_1(C_391) | k2_relset_1(u1_struct_0(A_390), u1_struct_0(B_389), C_391)!=k2_struct_0(B_389) | ~m1_subset_1(D_392, k1_zfmisc_1(u1_struct_0(A_390))) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_390), u1_struct_0(B_389)))) | ~v1_funct_2(C_391, u1_struct_0(A_390), u1_struct_0(B_389)) | ~v1_funct_1(C_391) | ~l1_struct_0(B_389) | ~l1_struct_0(A_390))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.13/2.83  tff(c_2951, plain, (![B_469, A_470, C_471, D_472]: (r1_tarski(k2_pre_topc(B_469, k7_relset_1(u1_struct_0(A_470), u1_struct_0(B_469), C_471, D_472)), k8_relset_1(u1_struct_0(B_469), u1_struct_0(A_470), k2_tops_2(u1_struct_0(A_470), u1_struct_0(B_469), C_471), k2_pre_topc(A_470, D_472))) | ~m1_subset_1(D_472, k1_zfmisc_1(u1_struct_0(A_470))) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_470), u1_struct_0(B_469), C_471), B_469, A_470) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_470), u1_struct_0(B_469), C_471), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_469), u1_struct_0(A_470)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_470), u1_struct_0(B_469), C_471), u1_struct_0(B_469), u1_struct_0(A_470)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_470), u1_struct_0(B_469), C_471)) | ~l1_pre_topc(A_470) | ~v2_pre_topc(A_470) | ~l1_pre_topc(B_469) | ~v2_pre_topc(B_469) | ~v2_funct_1(C_471) | k2_relset_1(u1_struct_0(A_470), u1_struct_0(B_469), C_471)!=k2_struct_0(B_469) | ~m1_subset_1(D_472, k1_zfmisc_1(u1_struct_0(A_470))) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_470), u1_struct_0(B_469)))) | ~v1_funct_2(C_471, u1_struct_0(A_470), u1_struct_0(B_469)) | ~v1_funct_1(C_471) | ~l1_struct_0(B_469) | ~l1_struct_0(A_470))), inference(superposition, [status(thm), theory('equality')], [c_2678, c_30])).
% 8.13/2.83  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.13/2.83  tff(c_3163, plain, (![B_502, A_503, C_504, D_505]: (k8_relset_1(u1_struct_0(B_502), u1_struct_0(A_503), k2_tops_2(u1_struct_0(A_503), u1_struct_0(B_502), C_504), k2_pre_topc(A_503, D_505))=k2_pre_topc(B_502, k7_relset_1(u1_struct_0(A_503), u1_struct_0(B_502), C_504, D_505)) | ~r1_tarski(k8_relset_1(u1_struct_0(B_502), u1_struct_0(A_503), k2_tops_2(u1_struct_0(A_503), u1_struct_0(B_502), C_504), k2_pre_topc(A_503, D_505)), k2_pre_topc(B_502, k7_relset_1(u1_struct_0(A_503), u1_struct_0(B_502), C_504, D_505))) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_503), u1_struct_0(B_502), C_504), B_502, A_503) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_503), u1_struct_0(B_502), C_504), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_502), u1_struct_0(A_503)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_503), u1_struct_0(B_502), C_504), u1_struct_0(B_502), u1_struct_0(A_503)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_503), u1_struct_0(B_502), C_504)) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | ~l1_pre_topc(B_502) | ~v2_pre_topc(B_502) | ~v2_funct_1(C_504) | k2_relset_1(u1_struct_0(A_503), u1_struct_0(B_502), C_504)!=k2_struct_0(B_502) | ~m1_subset_1(D_505, k1_zfmisc_1(u1_struct_0(A_503))) | ~m1_subset_1(C_504, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_503), u1_struct_0(B_502)))) | ~v1_funct_2(C_504, u1_struct_0(A_503), u1_struct_0(B_502)) | ~v1_funct_1(C_504) | ~l1_struct_0(B_502) | ~l1_struct_0(A_503))), inference(resolution, [status(thm)], [c_2951, c_2])).
% 8.13/2.83  tff(c_3169, plain, (![B_68, A_60, C_72, D_74]: (k8_relset_1(u1_struct_0(B_68), u1_struct_0(A_60), k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), k2_pre_topc(A_60, D_74))=k2_pre_topc(B_68, k7_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72, D_74)) | ~r1_tarski(k2_pre_topc(B_68, k7_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72, D_74)), k2_pre_topc(B_68, k7_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72, D_74))) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), B_68, A_60) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_68), u1_struct_0(A_60)))) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), u1_struct_0(B_68), u1_struct_0(A_60)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | ~l1_pre_topc(B_68) | ~v2_pre_topc(B_68) | ~v2_funct_1(C_72) | k2_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72)!=k2_struct_0(B_68) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60), u1_struct_0(B_68)))) | ~v1_funct_2(C_72, u1_struct_0(A_60), u1_struct_0(B_68)) | ~v1_funct_1(C_72) | ~l1_struct_0(B_68) | ~l1_struct_0(A_60) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_60))) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), B_68, A_60) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72), u1_struct_0(B_68), u1_struct_0(A_60)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_60), u1_struct_0(B_68), C_72)) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | ~l1_pre_topc(B_68) | ~v2_pre_topc(B_68) | v2_struct_0(B_68) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60), u1_struct_0(B_68)))) | ~v1_funct_2(C_72, u1_struct_0(A_60), u1_struct_0(B_68)) | ~v1_funct_1(C_72) | ~v2_funct_1(C_72) | k2_relset_1(u1_struct_0(A_60), u1_struct_0(B_68), C_72)!=k2_struct_0(B_68) | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0(A_60))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60), u1_struct_0(B_68)))) | ~v1_funct_2(C_72, u1_struct_0(A_60), u1_struct_0(B_68)) | ~v1_funct_1(C_72) | ~l1_struct_0(B_68) | ~l1_struct_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_2884, c_3163])).
% 8.13/2.83  tff(c_3182, plain, (![B_506, A_507, C_508, D_509]: (k8_relset_1(u1_struct_0(B_506), u1_struct_0(A_507), k2_tops_2(u1_struct_0(A_507), u1_struct_0(B_506), C_508), k2_pre_topc(A_507, D_509))=k2_pre_topc(B_506, k7_relset_1(u1_struct_0(A_507), u1_struct_0(B_506), C_508, D_509)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_507), u1_struct_0(B_506), C_508), B_506, A_507) | ~m1_subset_1(k2_tops_2(u1_struct_0(A_507), u1_struct_0(B_506), C_508), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_506), u1_struct_0(A_507)))) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_507), u1_struct_0(B_506), C_508), B_506, A_507) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_507), u1_struct_0(B_506), C_508), u1_struct_0(B_506), u1_struct_0(A_507)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_507), u1_struct_0(B_506), C_508)) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | ~l1_pre_topc(B_506) | ~v2_pre_topc(B_506) | v2_struct_0(B_506) | ~v2_funct_1(C_508) | k2_relset_1(u1_struct_0(A_507), u1_struct_0(B_506), C_508)!=k2_struct_0(B_506) | ~m1_subset_1(D_509, k1_zfmisc_1(u1_struct_0(A_507))) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_507), u1_struct_0(B_506)))) | ~v1_funct_2(C_508, u1_struct_0(A_507), u1_struct_0(B_506)) | ~v1_funct_1(C_508) | ~l1_struct_0(B_506) | ~l1_struct_0(A_507))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3169])).
% 8.13/2.83  tff(c_3187, plain, (![B_510, A_511, C_512, D_513]: (k8_relset_1(u1_struct_0(B_510), u1_struct_0(A_511), k2_tops_2(u1_struct_0(A_511), u1_struct_0(B_510), C_512), k2_pre_topc(A_511, D_513))=k2_pre_topc(B_510, k7_relset_1(u1_struct_0(A_511), u1_struct_0(B_510), C_512, D_513)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_511), u1_struct_0(B_510), C_512), B_510, A_511) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_511), u1_struct_0(B_510), C_512), B_510, A_511) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_511), u1_struct_0(B_510), C_512), u1_struct_0(B_510), u1_struct_0(A_511)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_511), u1_struct_0(B_510), C_512)) | ~l1_pre_topc(A_511) | ~v2_pre_topc(A_511) | ~l1_pre_topc(B_510) | ~v2_pre_topc(B_510) | v2_struct_0(B_510) | ~v2_funct_1(C_512) | k2_relset_1(u1_struct_0(A_511), u1_struct_0(B_510), C_512)!=k2_struct_0(B_510) | ~m1_subset_1(D_513, k1_zfmisc_1(u1_struct_0(A_511))) | ~l1_struct_0(B_510) | ~l1_struct_0(A_511) | ~m1_subset_1(C_512, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_511), u1_struct_0(B_510)))) | ~v1_funct_2(C_512, u1_struct_0(A_511), u1_struct_0(B_510)) | ~v1_funct_1(C_512))), inference(resolution, [status(thm)], [c_24, c_3182])).
% 8.13/2.83  tff(c_3325, plain, (![A_524, B_525, C_526, D_527]: (k7_relset_1(u1_struct_0(A_524), u1_struct_0(B_525), C_526, k2_pre_topc(A_524, D_527))=k2_pre_topc(B_525, k7_relset_1(u1_struct_0(A_524), u1_struct_0(B_525), C_526, D_527)) | ~v2_funct_1(C_526) | k2_relset_1(u1_struct_0(A_524), u1_struct_0(B_525), C_526)!=k2_struct_0(B_525) | ~m1_subset_1(k2_pre_topc(A_524, D_527), k1_zfmisc_1(u1_struct_0(A_524))) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_524), u1_struct_0(B_525)))) | ~v1_funct_2(C_526, u1_struct_0(A_524), u1_struct_0(B_525)) | ~v1_funct_1(C_526) | ~l1_struct_0(B_525) | ~l1_struct_0(A_524) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_524), u1_struct_0(B_525), C_526), B_525, A_524) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_524), u1_struct_0(B_525), C_526), B_525, A_524) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_524), u1_struct_0(B_525), C_526), u1_struct_0(B_525), u1_struct_0(A_524)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_524), u1_struct_0(B_525), C_526)) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | ~l1_pre_topc(B_525) | ~v2_pre_topc(B_525) | v2_struct_0(B_525) | ~v2_funct_1(C_526) | k2_relset_1(u1_struct_0(A_524), u1_struct_0(B_525), C_526)!=k2_struct_0(B_525) | ~m1_subset_1(D_527, k1_zfmisc_1(u1_struct_0(A_524))) | ~l1_struct_0(B_525) | ~l1_struct_0(A_524) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_524), u1_struct_0(B_525)))) | ~v1_funct_2(C_526, u1_struct_0(A_524), u1_struct_0(B_525)) | ~v1_funct_1(C_526))), inference(superposition, [status(thm), theory('equality')], [c_3187, c_42])).
% 8.13/2.83  tff(c_3333, plain, (![A_528, B_529, C_530, B_531]: (k7_relset_1(u1_struct_0(A_528), u1_struct_0(B_529), C_530, k2_pre_topc(A_528, B_531))=k2_pre_topc(B_529, k7_relset_1(u1_struct_0(A_528), u1_struct_0(B_529), C_530, B_531)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(A_528), u1_struct_0(B_529), C_530), B_529, A_528) | ~v3_tops_2(k2_tops_2(u1_struct_0(A_528), u1_struct_0(B_529), C_530), B_529, A_528) | ~v1_funct_2(k2_tops_2(u1_struct_0(A_528), u1_struct_0(B_529), C_530), u1_struct_0(B_529), u1_struct_0(A_528)) | ~v1_funct_1(k2_tops_2(u1_struct_0(A_528), u1_struct_0(B_529), C_530)) | ~v2_pre_topc(A_528) | ~l1_pre_topc(B_529) | ~v2_pre_topc(B_529) | v2_struct_0(B_529) | ~v2_funct_1(C_530) | k2_relset_1(u1_struct_0(A_528), u1_struct_0(B_529), C_530)!=k2_struct_0(B_529) | ~l1_struct_0(B_529) | ~l1_struct_0(A_528) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_528), u1_struct_0(B_529)))) | ~v1_funct_2(C_530, u1_struct_0(A_528), u1_struct_0(B_529)) | ~v1_funct_1(C_530) | ~m1_subset_1(B_531, k1_zfmisc_1(u1_struct_0(A_528))) | ~l1_pre_topc(A_528))), inference(resolution, [status(thm)], [c_8, c_3325])).
% 8.13/2.83  tff(c_3338, plain, (![B_531]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', B_531))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', B_531)) | ~v5_pre_topc(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v3_tops_2(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6'), '#skF_5', '#skF_4') | ~v1_funct_1(k2_tops_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')) | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(B_531, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_2536, c_3333])).
% 8.13/2.83  tff(c_3342, plain, (![B_531]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', B_531))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', B_531)) | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | ~m1_subset_1(B_531, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_62, c_60, c_58, c_114, c_106, c_66, c_64, c_72, c_131, c_2626, c_2614, c_3338])).
% 8.13/2.83  tff(c_3343, plain, (![B_531]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', B_531))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', B_531)) | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | ~m1_subset_1(B_531, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_3342])).
% 8.13/2.83  tff(c_3344, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3343])).
% 8.13/2.83  tff(c_3347, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_10, c_3344])).
% 8.13/2.83  tff(c_3351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_3347])).
% 8.13/2.83  tff(c_3352, plain, (![B_531]: (~l1_struct_0('#skF_5') | k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', B_531))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', B_531)) | ~m1_subset_1(B_531, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_3343])).
% 8.13/2.83  tff(c_3354, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_3352])).
% 8.13/2.83  tff(c_3357, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_10, c_3354])).
% 8.13/2.83  tff(c_3361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_3357])).
% 8.13/2.83  tff(c_3364, plain, (![B_532]: (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', B_532))=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', B_532)) | ~m1_subset_1(B_532, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_3352])).
% 8.13/2.83  tff(c_76, plain, (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', '#skF_7'))!=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_7')) | ~v2_funct_1('#skF_6') | k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5') | k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 8.13/2.83  tff(c_2571, plain, (k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_pre_topc('#skF_4', '#skF_7'))!=k2_pre_topc('#skF_5', k7_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2530, c_119, c_114, c_106, c_76])).
% 8.13/2.83  tff(c_3399, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3364, c_2571])).
% 8.13/2.83  tff(c_3434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2529, c_3399])).
% 8.13/2.83  tff(c_3436, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_98])).
% 8.13/2.83  tff(c_3435, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_98])).
% 8.13/2.83  tff(c_3486, plain, (![A_550, B_551, C_552]: (k1_relset_1(u1_struct_0(A_550), u1_struct_0(B_551), C_552)=k2_struct_0(A_550) | ~v3_tops_2(C_552, A_550, B_551) | ~m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_550), u1_struct_0(B_551)))) | ~v1_funct_2(C_552, u1_struct_0(A_550), u1_struct_0(B_551)) | ~v1_funct_1(C_552) | ~l1_pre_topc(B_551) | ~l1_pre_topc(A_550))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.13/2.83  tff(c_3493, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3486])).
% 8.13/2.83  tff(c_3497, plain, (k1_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_3435, c_3493])).
% 8.13/2.83  tff(c_3499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3436, c_3497])).
% 8.13/2.83  tff(c_3501, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')!=k2_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_92])).
% 8.13/2.83  tff(c_3500, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_92])).
% 8.13/2.83  tff(c_3556, plain, (![A_570, B_571, C_572]: (k2_relset_1(u1_struct_0(A_570), u1_struct_0(B_571), C_572)=k2_struct_0(B_571) | ~v3_tops_2(C_572, A_570, B_571) | ~m1_subset_1(C_572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_570), u1_struct_0(B_571)))) | ~v1_funct_2(C_572, u1_struct_0(A_570), u1_struct_0(B_571)) | ~v1_funct_1(C_572) | ~l1_pre_topc(B_571) | ~l1_pre_topc(A_570))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.13/2.83  tff(c_3563, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3556])).
% 8.13/2.83  tff(c_3567, plain, (k2_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6')=k2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_3500, c_3563])).
% 8.13/2.83  tff(c_3569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3501, c_3567])).
% 8.13/2.83  tff(c_3571, plain, (~v2_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_86])).
% 8.13/2.83  tff(c_3570, plain, (v3_tops_2('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 8.13/2.83  tff(c_3603, plain, (![C_586, A_587, B_588]: (v2_funct_1(C_586) | ~v3_tops_2(C_586, A_587, B_588) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_587), u1_struct_0(B_588)))) | ~v1_funct_2(C_586, u1_struct_0(A_587), u1_struct_0(B_588)) | ~v1_funct_1(C_586) | ~l1_pre_topc(B_588) | ~l1_pre_topc(A_587))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.13/2.83  tff(c_3610, plain, (v2_funct_1('#skF_6') | ~v3_tops_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_3603])).
% 8.13/2.83  tff(c_3614, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_62, c_60, c_3570, c_3610])).
% 8.13/2.83  tff(c_3616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3571, c_3614])).
% 8.13/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.13/2.83  
% 8.13/2.83  Inference rules
% 8.13/2.83  ----------------------
% 8.13/2.83  #Ref     : 0
% 8.13/2.83  #Sup     : 860
% 8.13/2.83  #Fact    : 0
% 8.13/2.83  #Define  : 0
% 8.13/2.83  #Split   : 18
% 8.13/2.83  #Chain   : 0
% 8.13/2.83  #Close   : 0
% 8.13/2.83  
% 8.13/2.83  Ordering : KBO
% 8.13/2.83  
% 8.13/2.83  Simplification rules
% 8.13/2.83  ----------------------
% 8.13/2.83  #Subsume      : 195
% 8.13/2.83  #Demod        : 921
% 8.13/2.83  #Tautology    : 160
% 8.13/2.83  #SimpNegUnit  : 44
% 8.13/2.83  #BackRed      : 0
% 8.13/2.83  
% 8.13/2.83  #Partial instantiations: 0
% 8.13/2.83  #Strategies tried      : 1
% 8.13/2.83  
% 8.13/2.83  Timing (in seconds)
% 8.13/2.83  ----------------------
% 8.13/2.83  Preprocessing        : 0.44
% 8.13/2.83  Parsing              : 0.23
% 8.13/2.83  CNF conversion       : 0.04
% 8.13/2.83  Main loop            : 1.50
% 8.13/2.83  Inferencing          : 0.55
% 8.13/2.83  Reduction            : 0.50
% 8.13/2.83  Demodulation         : 0.37
% 8.13/2.83  BG Simplification    : 0.09
% 8.13/2.83  Subsumption          : 0.30
% 8.13/2.83  Abstraction          : 0.08
% 8.13/2.84  MUC search           : 0.00
% 8.13/2.84  Cooper               : 0.00
% 8.13/2.84  Total                : 2.04
% 8.13/2.84  Index Insertion      : 0.00
% 8.13/2.84  Index Deletion       : 0.00
% 8.13/2.84  Index Matching       : 0.00
% 8.13/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
