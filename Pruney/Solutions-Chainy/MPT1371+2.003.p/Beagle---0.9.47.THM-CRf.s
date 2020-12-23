%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:00 EST 2020

% Result     : Theorem 12.40s
% Output     : CNFRefutation 12.47s
% Verified   : 
% Statistics : Number of formulae       :  167 (19778 expanded)
%              Number of leaves         :   50 (6962 expanded)
%              Depth                    :   26
%              Number of atoms          :  579 (69868 expanded)
%              Number of equality atoms :   91 (15767 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_relat_1 > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_200,negated_conjecture,(
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
               => ( ( v1_compts_1(A)
                    & v8_pre_topc(B)
                    & k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                    & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C)
                    & v5_pre_topc(C,A,B) )
                 => v3_tops_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_compts_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_132,axiom,(
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
              <=> ( k1_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(A)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C)
                  & ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ( v4_pre_topc(D,A)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_2)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_166,axiom,(
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
             => ( ( v1_compts_1(A)
                  & v8_pre_topc(B)
                  & k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v5_pre_topc(C,A,B) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( v4_pre_topc(D,A)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_94,axiom,(
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

tff(c_60,plain,(
    ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_86,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_36,plain,(
    ! [A_50] :
      ( l1_struct_0(A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_90,plain,(
    ! [A_93] :
      ( u1_struct_0(A_93) = k2_struct_0(A_93)
      | ~ l1_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_95,plain,(
    ! [A_94] :
      ( u1_struct_0(A_94) = k2_struct_0(A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_103,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_95])).

tff(c_80,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_102,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_95])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_125,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_102,c_74])).

tff(c_135,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_143,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_135])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_152,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_160,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_152])).

tff(c_68,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_130,plain,(
    k1_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_102,c_68])).

tff(c_162,plain,(
    k2_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_130])).

tff(c_169,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_125])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] :
      ( k2_relset_1(A_15,B_16,C_17) = k2_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_208,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_169,c_14])).

tff(c_66,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_115,plain,(
    k2_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_102,c_66])).

tff(c_170,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_115])).

tff(c_219,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_170])).

tff(c_76,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_105,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_76])).

tff(c_114,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_105])).

tff(c_171,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_114])).

tff(c_228,plain,(
    v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_171])).

tff(c_225,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_169])).

tff(c_167,plain,(
    k1_relset_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_160])).

tff(c_226,plain,(
    k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_167])).

tff(c_224,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_208])).

tff(c_64,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_265,plain,(
    ! [A_112] :
      ( m1_subset_1(A_112,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_112),k2_relat_1(A_112))))
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_281,plain,(
    ! [A_112] :
      ( r1_tarski(A_112,k2_zfmisc_1(k1_relat_1(A_112),k2_relat_1(A_112)))
      | ~ v1_funct_1(A_112)
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_265,c_2])).

tff(c_172,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_103])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_229,plain,(
    u1_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_102])).

tff(c_1814,plain,(
    ! [A_356,B_357,C_358] :
      ( m1_subset_1('#skF_2'(A_356,B_357,C_358),k1_zfmisc_1(u1_struct_0(A_356)))
      | v3_tops_2(C_358,A_356,B_357)
      | ~ v2_funct_1(C_358)
      | k2_relset_1(u1_struct_0(A_356),u1_struct_0(B_357),C_358) != k2_struct_0(B_357)
      | k1_relset_1(u1_struct_0(A_356),u1_struct_0(B_357),C_358) != k2_struct_0(A_356)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356),u1_struct_0(B_357))))
      | ~ v1_funct_2(C_358,u1_struct_0(A_356),u1_struct_0(B_357))
      | ~ v1_funct_1(C_358)
      | ~ l1_pre_topc(B_357)
      | v2_struct_0(B_357)
      | ~ l1_pre_topc(A_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1821,plain,(
    ! [A_356,C_358] :
      ( m1_subset_1('#skF_2'(A_356,'#skF_4',C_358),k1_zfmisc_1(u1_struct_0(A_356)))
      | v3_tops_2(C_358,A_356,'#skF_4')
      | ~ v2_funct_1(C_358)
      | k2_relset_1(u1_struct_0(A_356),u1_struct_0('#skF_4'),C_358) != k2_struct_0('#skF_4')
      | k1_relset_1(u1_struct_0(A_356),u1_struct_0('#skF_4'),C_358) != k2_struct_0(A_356)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_358,u1_struct_0(A_356),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_358)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_356) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_1814])).

tff(c_1833,plain,(
    ! [A_356,C_358] :
      ( m1_subset_1('#skF_2'(A_356,'#skF_4',C_358),k1_zfmisc_1(u1_struct_0(A_356)))
      | v3_tops_2(C_358,A_356,'#skF_4')
      | ~ v2_funct_1(C_358)
      | k2_relset_1(u1_struct_0(A_356),k2_relat_1('#skF_5'),C_358) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_356),k2_relat_1('#skF_5'),C_358) != k2_struct_0(A_356)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_358,u1_struct_0(A_356),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_358)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_356) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_229,c_229,c_229,c_219,c_1821])).

tff(c_1905,plain,(
    ! [A_363,C_364] :
      ( m1_subset_1('#skF_2'(A_363,'#skF_4',C_364),k1_zfmisc_1(u1_struct_0(A_363)))
      | v3_tops_2(C_364,A_363,'#skF_4')
      | ~ v2_funct_1(C_364)
      | k2_relset_1(u1_struct_0(A_363),k2_relat_1('#skF_5'),C_364) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_363),k2_relat_1('#skF_5'),C_364) != k2_struct_0(A_363)
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_364,u1_struct_0(A_363),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_364)
      | ~ l1_pre_topc(A_363) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1833])).

tff(c_2703,plain,(
    ! [A_467,A_468] :
      ( m1_subset_1('#skF_2'(A_467,'#skF_4',A_468),k1_zfmisc_1(u1_struct_0(A_467)))
      | v3_tops_2(A_468,A_467,'#skF_4')
      | ~ v2_funct_1(A_468)
      | k2_relset_1(u1_struct_0(A_467),k2_relat_1('#skF_5'),A_468) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_467),k2_relat_1('#skF_5'),A_468) != k2_struct_0(A_467)
      | ~ v1_funct_2(A_468,u1_struct_0(A_467),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_468)
      | ~ l1_pre_topc(A_467)
      | ~ r1_tarski(A_468,k2_zfmisc_1(u1_struct_0(A_467),k2_relat_1('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1905])).

tff(c_2713,plain,(
    ! [A_468] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4',A_468),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v3_tops_2(A_468,'#skF_3','#skF_4')
      | ~ v2_funct_1(A_468)
      | k2_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),A_468) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),A_468) != k2_struct_0('#skF_3')
      | ~ v1_funct_2(A_468,u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_468)
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_468,k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2703])).

tff(c_3960,plain,(
    ! [A_652] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4',A_652),k1_zfmisc_1(k1_relat_1('#skF_5')))
      | v3_tops_2(A_652,'#skF_3','#skF_4')
      | ~ v2_funct_1(A_652)
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_652) != k2_relat_1('#skF_5')
      | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_652) != k1_relat_1('#skF_5')
      | ~ v1_funct_2(A_652,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_652)
      | ~ r1_tarski(A_652,k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_172,c_172,c_162,c_172,c_172,c_2713])).

tff(c_3976,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k1_relat_1('#skF_5')))
    | v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k1_relat_1('#skF_5')
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_281,c_3960])).

tff(c_3985,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k1_relat_1('#skF_5')))
    | v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_78,c_228,c_226,c_224,c_64,c_3976])).

tff(c_3986,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k1_relat_1('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3985])).

tff(c_129,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_168,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_129])).

tff(c_227,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_168])).

tff(c_62,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_20,plain,(
    ! [A_26] :
      ( m1_subset_1(A_26,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_26),k2_relat_1(A_26))))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_288,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k7_relset_1(A_113,B_114,C_115,D_116) = k9_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_296,plain,(
    ! [A_26,D_116] :
      ( k7_relset_1(k1_relat_1(A_26),k2_relat_1(A_26),A_26,D_116) = k9_relat_1(A_26,D_116)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_20,c_288])).

tff(c_88,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_72,plain,(
    v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_82,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_70,plain,(
    v8_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_2003,plain,(
    ! [A_373,B_374,C_375,D_376] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_373),u1_struct_0(B_374),C_375,D_376),B_374)
      | ~ v4_pre_topc(D_376,A_373)
      | ~ m1_subset_1(D_376,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ v5_pre_topc(C_375,A_373,B_374)
      | k2_relset_1(u1_struct_0(A_373),u1_struct_0(B_374),C_375) != k2_struct_0(B_374)
      | ~ v8_pre_topc(B_374)
      | ~ v1_compts_1(A_373)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_373),u1_struct_0(B_374))))
      | ~ v1_funct_2(C_375,u1_struct_0(A_373),u1_struct_0(B_374))
      | ~ v1_funct_1(C_375)
      | ~ l1_pre_topc(B_374)
      | ~ v2_pre_topc(B_374)
      | v2_struct_0(B_374)
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2010,plain,(
    ! [A_373,C_375,D_376] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_373),u1_struct_0('#skF_4'),C_375,D_376),'#skF_4')
      | ~ v4_pre_topc(D_376,A_373)
      | ~ m1_subset_1(D_376,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ v5_pre_topc(C_375,A_373,'#skF_4')
      | k2_relset_1(u1_struct_0(A_373),u1_struct_0('#skF_4'),C_375) != k2_struct_0('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v1_compts_1(A_373)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_373),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_375,u1_struct_0(A_373),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_375)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_2003])).

tff(c_2022,plain,(
    ! [A_373,C_375,D_376] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_373),k2_relat_1('#skF_5'),C_375,D_376),'#skF_4')
      | ~ v4_pre_topc(D_376,A_373)
      | ~ m1_subset_1(D_376,k1_zfmisc_1(u1_struct_0(A_373)))
      | ~ v5_pre_topc(C_375,A_373,'#skF_4')
      | k2_relset_1(u1_struct_0(A_373),k2_relat_1('#skF_5'),C_375) != k2_relat_1('#skF_5')
      | ~ v1_compts_1(A_373)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_373),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_375,u1_struct_0(A_373),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_375)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_229,c_70,c_229,c_219,c_229,c_2010])).

tff(c_2088,plain,(
    ! [A_384,C_385,D_386] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_384),k2_relat_1('#skF_5'),C_385,D_386),'#skF_4')
      | ~ v4_pre_topc(D_386,A_384)
      | ~ m1_subset_1(D_386,k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ v5_pre_topc(C_385,A_384,'#skF_4')
      | k2_relset_1(u1_struct_0(A_384),k2_relat_1('#skF_5'),C_385) != k2_relat_1('#skF_5')
      | ~ v1_compts_1(A_384)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_384),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_385,u1_struct_0(A_384),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_385)
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2022])).

tff(c_2774,plain,(
    ! [A_489,A_490,D_491] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(A_489),k2_relat_1('#skF_5'),A_490,D_491),'#skF_4')
      | ~ v4_pre_topc(D_491,A_489)
      | ~ m1_subset_1(D_491,k1_zfmisc_1(u1_struct_0(A_489)))
      | ~ v5_pre_topc(A_490,A_489,'#skF_4')
      | k2_relset_1(u1_struct_0(A_489),k2_relat_1('#skF_5'),A_490) != k2_relat_1('#skF_5')
      | ~ v1_compts_1(A_489)
      | ~ v1_funct_2(A_490,u1_struct_0(A_489),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_490)
      | ~ l1_pre_topc(A_489)
      | ~ v2_pre_topc(A_489)
      | ~ r1_tarski(A_490,k2_zfmisc_1(u1_struct_0(A_489),k2_relat_1('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_2088])).

tff(c_2786,plain,(
    ! [A_490,D_491] :
      ( v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_490,D_491),'#skF_4')
      | ~ v4_pre_topc(D_491,'#skF_3')
      | ~ m1_subset_1(D_491,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(A_490,'#skF_3','#skF_4')
      | k2_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),A_490) != k2_relat_1('#skF_5')
      | ~ v1_compts_1('#skF_3')
      | ~ v1_funct_2(A_490,u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_490)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ r1_tarski(A_490,k2_zfmisc_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2774])).

tff(c_3232,plain,(
    ! [A_588,D_589] :
      ( v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_588,D_589),'#skF_4')
      | ~ v4_pre_topc(D_589,'#skF_3')
      | ~ m1_subset_1(D_589,k1_zfmisc_1(k1_relat_1('#skF_5')))
      | ~ v5_pre_topc(A_588,'#skF_3','#skF_4')
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_588) != k2_relat_1('#skF_5')
      | ~ v1_funct_2(A_588,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_588)
      | ~ r1_tarski(A_588,k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_88,c_86,c_172,c_72,c_172,c_172,c_2786])).

tff(c_3238,plain,(
    ! [D_116] :
      ( v4_pre_topc(k9_relat_1('#skF_5',D_116),'#skF_4')
      | ~ v4_pre_topc(D_116,'#skF_3')
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k1_relat_1('#skF_5')))
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
      | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_3232])).

tff(c_3244,plain,(
    ! [D_116] :
      ( v4_pre_topc(k9_relat_1('#skF_5',D_116),'#skF_4')
      | ~ v4_pre_topc(D_116,'#skF_3')
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k1_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_78,c_227,c_78,c_228,c_224,c_62,c_3238])).

tff(c_4044,plain,
    ( v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3986,c_3244])).

tff(c_4052,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4044])).

tff(c_297,plain,(
    ! [D_116] : k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5',D_116) = k9_relat_1('#skF_5',D_116) ),
    inference(resolution,[status(thm)],[c_225,c_288])).

tff(c_354,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( m1_subset_1(k7_relset_1(A_126,B_127,C_128,D_129),k1_zfmisc_1(B_127))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_375,plain,(
    ! [D_116] :
      ( m1_subset_1(k9_relat_1('#skF_5',D_116),k1_zfmisc_1(k2_relat_1('#skF_5')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_354])).

tff(c_383,plain,(
    ! [D_130] : m1_subset_1(k9_relat_1('#skF_5',D_130),k1_zfmisc_1(k2_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_375])).

tff(c_387,plain,(
    ! [D_130] : r1_tarski(k9_relat_1('#skF_5',D_130),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_383,c_2])).

tff(c_4045,plain,(
    r1_tarski('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3986,c_2])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k10_relat_1(B_4,k9_relat_1(B_4,A_3)) = A_3
      | ~ v2_funct_1(B_4)
      | ~ r1_tarski(A_3,k1_relat_1(B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4047,plain,
    ( k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4045,c_6])).

tff(c_4050,plain,(
    k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) = '#skF_2'('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_78,c_64,c_4047])).

tff(c_410,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k8_relset_1(A_133,B_134,C_135,D_136) = k10_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_422,plain,(
    ! [A_26,D_136] :
      ( k8_relset_1(k1_relat_1(A_26),k2_relat_1(A_26),A_26,D_136) = k10_relat_1(A_26,D_136)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_20,c_410])).

tff(c_1278,plain,(
    ! [A_302,B_303,C_304,D_305] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_302),u1_struct_0(B_303),C_304,D_305),A_302)
      | ~ v4_pre_topc(D_305,B_303)
      | ~ m1_subset_1(D_305,k1_zfmisc_1(u1_struct_0(B_303)))
      | ~ v5_pre_topc(C_304,A_302,B_303)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_302),u1_struct_0(B_303))))
      | ~ v1_funct_2(C_304,u1_struct_0(A_302),u1_struct_0(B_303))
      | ~ v1_funct_1(C_304)
      | ~ l1_pre_topc(B_303)
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2505,plain,(
    ! [A_435,B_436,A_437,D_438] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_435),u1_struct_0(B_436),A_437,D_438),A_435)
      | ~ v4_pre_topc(D_438,B_436)
      | ~ m1_subset_1(D_438,k1_zfmisc_1(u1_struct_0(B_436)))
      | ~ v5_pre_topc(A_437,A_435,B_436)
      | ~ v1_funct_2(A_437,u1_struct_0(A_435),u1_struct_0(B_436))
      | ~ v1_funct_1(A_437)
      | ~ l1_pre_topc(B_436)
      | ~ l1_pre_topc(A_435)
      | ~ r1_tarski(A_437,k2_zfmisc_1(u1_struct_0(A_435),u1_struct_0(B_436))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1278])).

tff(c_2518,plain,(
    ! [B_436,A_437,D_438] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'),u1_struct_0(B_436),A_437,D_438),'#skF_3')
      | ~ v4_pre_topc(D_438,B_436)
      | ~ m1_subset_1(D_438,k1_zfmisc_1(u1_struct_0(B_436)))
      | ~ v5_pre_topc(A_437,'#skF_3',B_436)
      | ~ v1_funct_2(A_437,u1_struct_0('#skF_3'),u1_struct_0(B_436))
      | ~ v1_funct_1(A_437)
      | ~ l1_pre_topc(B_436)
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_437,k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_436))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2505])).

tff(c_2648,plain,(
    ! [B_461,A_462,D_463] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'),u1_struct_0(B_461),A_462,D_463),'#skF_3')
      | ~ v4_pre_topc(D_463,B_461)
      | ~ m1_subset_1(D_463,k1_zfmisc_1(u1_struct_0(B_461)))
      | ~ v5_pre_topc(A_462,'#skF_3',B_461)
      | ~ v1_funct_2(A_462,k1_relat_1('#skF_5'),u1_struct_0(B_461))
      | ~ v1_funct_1(A_462)
      | ~ l1_pre_topc(B_461)
      | ~ r1_tarski(A_462,k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0(B_461))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_86,c_172,c_2518])).

tff(c_2655,plain,(
    ! [A_462,D_463] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_462,D_463),'#skF_3')
      | ~ v4_pre_topc(D_463,'#skF_4')
      | ~ m1_subset_1(D_463,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v5_pre_topc(A_462,'#skF_3','#skF_4')
      | ~ v1_funct_2(A_462,k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(A_462)
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_462,k2_zfmisc_1(k1_relat_1('#skF_5'),u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_2648])).

tff(c_2664,plain,(
    ! [A_464,D_465] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),A_464,D_465),'#skF_3')
      | ~ v4_pre_topc(D_465,'#skF_4')
      | ~ m1_subset_1(D_465,k1_zfmisc_1(k2_relat_1('#skF_5')))
      | ~ v5_pre_topc(A_464,'#skF_3','#skF_4')
      | ~ v1_funct_2(A_464,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(A_464)
      | ~ r1_tarski(A_464,k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_80,c_229,c_229,c_2655])).

tff(c_2672,plain,(
    ! [D_136] :
      ( v4_pre_topc(k10_relat_1('#skF_5',D_136),'#skF_3')
      | ~ v4_pre_topc(D_136,'#skF_4')
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_relat_1('#skF_5')))
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5')))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_2664])).

tff(c_2681,plain,(
    ! [D_466] :
      ( v4_pre_topc(k10_relat_1('#skF_5',D_466),'#skF_3')
      | ~ v4_pre_topc(D_466,'#skF_4')
      | ~ m1_subset_1(D_466,k1_zfmisc_1(k2_relat_1('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_78,c_227,c_78,c_228,c_62,c_2672])).

tff(c_2702,plain,(
    ! [A_1] :
      ( v4_pre_topc(k10_relat_1('#skF_5',A_1),'#skF_3')
      | ~ v4_pre_topc(A_1,'#skF_4')
      | ~ r1_tarski(A_1,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4,c_2681])).

tff(c_4056,plain,
    ( v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),k2_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4050,c_2702])).

tff(c_4063,plain,
    ( v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | ~ v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_4056])).

tff(c_4064,plain,(
    ~ v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4052,c_4063])).

tff(c_2194,plain,(
    ! [A_395,B_396,C_397] :
      ( v4_pre_topc('#skF_2'(A_395,B_396,C_397),A_395)
      | v4_pre_topc(k7_relset_1(u1_struct_0(A_395),u1_struct_0(B_396),C_397,'#skF_2'(A_395,B_396,C_397)),B_396)
      | v3_tops_2(C_397,A_395,B_396)
      | ~ v2_funct_1(C_397)
      | k2_relset_1(u1_struct_0(A_395),u1_struct_0(B_396),C_397) != k2_struct_0(B_396)
      | k1_relset_1(u1_struct_0(A_395),u1_struct_0(B_396),C_397) != k2_struct_0(A_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),u1_struct_0(B_396))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_395),u1_struct_0(B_396))
      | ~ v1_funct_1(C_397)
      | ~ l1_pre_topc(B_396)
      | v2_struct_0(B_396)
      | ~ l1_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2202,plain,(
    ! [A_395,C_397] :
      ( v4_pre_topc('#skF_2'(A_395,'#skF_4',C_397),A_395)
      | v4_pre_topc(k7_relset_1(u1_struct_0(A_395),k2_relat_1('#skF_5'),C_397,'#skF_2'(A_395,'#skF_4',C_397)),'#skF_4')
      | v3_tops_2(C_397,A_395,'#skF_4')
      | ~ v2_funct_1(C_397)
      | k2_relset_1(u1_struct_0(A_395),u1_struct_0('#skF_4'),C_397) != k2_struct_0('#skF_4')
      | k1_relset_1(u1_struct_0(A_395),u1_struct_0('#skF_4'),C_397) != k2_struct_0(A_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_395),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_397)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_395) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_2194])).

tff(c_2213,plain,(
    ! [A_395,C_397] :
      ( v4_pre_topc('#skF_2'(A_395,'#skF_4',C_397),A_395)
      | v4_pre_topc(k7_relset_1(u1_struct_0(A_395),k2_relat_1('#skF_5'),C_397,'#skF_2'(A_395,'#skF_4',C_397)),'#skF_4')
      | v3_tops_2(C_397,A_395,'#skF_4')
      | ~ v2_funct_1(C_397)
      | k2_relset_1(u1_struct_0(A_395),k2_relat_1('#skF_5'),C_397) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_395),k2_relat_1('#skF_5'),C_397) != k2_struct_0(A_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_397,u1_struct_0(A_395),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_397)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_229,c_229,c_229,c_229,c_219,c_2202])).

tff(c_2285,plain,(
    ! [A_404,C_405] :
      ( v4_pre_topc('#skF_2'(A_404,'#skF_4',C_405),A_404)
      | v4_pre_topc(k7_relset_1(u1_struct_0(A_404),k2_relat_1('#skF_5'),C_405,'#skF_2'(A_404,'#skF_4',C_405)),'#skF_4')
      | v3_tops_2(C_405,A_404,'#skF_4')
      | ~ v2_funct_1(C_405)
      | k2_relset_1(u1_struct_0(A_404),k2_relat_1('#skF_5'),C_405) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_404),k2_relat_1('#skF_5'),C_405) != k2_struct_0(A_404)
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_405,u1_struct_0(A_404),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_405)
      | ~ l1_pre_topc(A_404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2213])).

tff(c_2293,plain,(
    ! [C_405] :
      ( v4_pre_topc('#skF_2'('#skF_3','#skF_4',C_405),'#skF_3')
      | v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_405,'#skF_2'('#skF_3','#skF_4',C_405)),'#skF_4')
      | v3_tops_2(C_405,'#skF_3','#skF_4')
      | ~ v2_funct_1(C_405)
      | k2_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),C_405) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),C_405) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(C_405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_405,u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_405)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2285])).

tff(c_8916,plain,(
    ! [C_979] :
      ( v4_pre_topc('#skF_2'('#skF_3','#skF_4',C_979),'#skF_3')
      | v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_979,'#skF_2'('#skF_3','#skF_4',C_979)),'#skF_4')
      | v3_tops_2(C_979,'#skF_3','#skF_4')
      | ~ v2_funct_1(C_979)
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_979) != k2_relat_1('#skF_5')
      | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_979) != k1_relat_1('#skF_5')
      | ~ m1_subset_1(C_979,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_979,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_979) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_172,c_172,c_172,c_162,c_172,c_2293])).

tff(c_8930,plain,
    ( v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_8916])).

tff(c_8937,plain,
    ( v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_78,c_78,c_228,c_225,c_226,c_224,c_64,c_8930])).

tff(c_8939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4064,c_4052,c_8937])).

tff(c_8941,plain,(
    v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_4044])).

tff(c_8940,plain,(
    v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4044])).

tff(c_2397,plain,(
    ! [A_417,B_418,C_419] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_417),u1_struct_0(B_418),C_419,'#skF_2'(A_417,B_418,C_419)),B_418)
      | ~ v4_pre_topc('#skF_2'(A_417,B_418,C_419),A_417)
      | v3_tops_2(C_419,A_417,B_418)
      | ~ v2_funct_1(C_419)
      | k2_relset_1(u1_struct_0(A_417),u1_struct_0(B_418),C_419) != k2_struct_0(B_418)
      | k1_relset_1(u1_struct_0(A_417),u1_struct_0(B_418),C_419) != k2_struct_0(A_417)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417),u1_struct_0(B_418))))
      | ~ v1_funct_2(C_419,u1_struct_0(A_417),u1_struct_0(B_418))
      | ~ v1_funct_1(C_419)
      | ~ l1_pre_topc(B_418)
      | v2_struct_0(B_418)
      | ~ l1_pre_topc(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2406,plain,(
    ! [A_417,C_419] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_417),k2_relat_1('#skF_5'),C_419,'#skF_2'(A_417,'#skF_4',C_419)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'(A_417,'#skF_4',C_419),A_417)
      | v3_tops_2(C_419,A_417,'#skF_4')
      | ~ v2_funct_1(C_419)
      | k2_relset_1(u1_struct_0(A_417),u1_struct_0('#skF_4'),C_419) != k2_struct_0('#skF_4')
      | k1_relset_1(u1_struct_0(A_417),u1_struct_0('#skF_4'),C_419) != k2_struct_0(A_417)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_419,u1_struct_0(A_417),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_419)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_417) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_2397])).

tff(c_2417,plain,(
    ! [A_417,C_419] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_417),k2_relat_1('#skF_5'),C_419,'#skF_2'(A_417,'#skF_4',C_419)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'(A_417,'#skF_4',C_419),A_417)
      | v3_tops_2(C_419,A_417,'#skF_4')
      | ~ v2_funct_1(C_419)
      | k2_relset_1(u1_struct_0(A_417),k2_relat_1('#skF_5'),C_419) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_417),k2_relat_1('#skF_5'),C_419) != k2_struct_0(A_417)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_419,u1_struct_0(A_417),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_419)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_229,c_229,c_229,c_229,c_219,c_2406])).

tff(c_2448,plain,(
    ! [A_424,C_425] :
      ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(A_424),k2_relat_1('#skF_5'),C_425,'#skF_2'(A_424,'#skF_4',C_425)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'(A_424,'#skF_4',C_425),A_424)
      | v3_tops_2(C_425,A_424,'#skF_4')
      | ~ v2_funct_1(C_425)
      | k2_relset_1(u1_struct_0(A_424),k2_relat_1('#skF_5'),C_425) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0(A_424),k2_relat_1('#skF_5'),C_425) != k2_struct_0(A_424)
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_424),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_425,u1_struct_0(A_424),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_425)
      | ~ l1_pre_topc(A_424) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2417])).

tff(c_2457,plain,(
    ! [C_425] :
      ( ~ v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_425,'#skF_2'('#skF_3','#skF_4',C_425)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4',C_425),'#skF_3')
      | v3_tops_2(C_425,'#skF_3','#skF_4')
      | ~ v2_funct_1(C_425)
      | k2_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),C_425) != k2_relat_1('#skF_5')
      | k1_relset_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'),C_425) != k2_struct_0('#skF_3')
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_425,u1_struct_0('#skF_3'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_425)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_2448])).

tff(c_13866,plain,(
    ! [C_1307] :
      ( ~ v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1307,'#skF_2'('#skF_3','#skF_4',C_1307)),'#skF_4')
      | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4',C_1307),'#skF_3')
      | v3_tops_2(C_1307,'#skF_3','#skF_4')
      | ~ v2_funct_1(C_1307)
      | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1307) != k2_relat_1('#skF_5')
      | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),C_1307) != k1_relat_1('#skF_5')
      | ~ m1_subset_1(C_1307,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
      | ~ v1_funct_2(C_1307,k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
      | ~ v1_funct_1(C_1307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_172,c_172,c_172,c_162,c_172,c_2457])).

tff(c_13889,plain,
    ( ~ v4_pre_topc(k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | ~ v4_pre_topc('#skF_2'('#skF_3','#skF_4','#skF_5'),'#skF_3')
    | v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k2_relat_1('#skF_5')
    | k1_relset_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'),'#skF_5') != k1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))))
    | ~ v1_funct_2('#skF_5',k1_relat_1('#skF_5'),k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_13866])).

tff(c_13898,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_78,c_78,c_228,c_225,c_226,c_224,c_64,c_8941,c_8940,c_13889])).

tff(c_13900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.40/5.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.47/5.27  
% 12.47/5.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.47/5.28  %$ v5_pre_topc > v3_tops_2 > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v8_pre_topc > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_relat_1 > v1_funct_1 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 12.47/5.28  
% 12.47/5.28  %Foreground sorts:
% 12.47/5.28  
% 12.47/5.28  
% 12.47/5.28  %Background operators:
% 12.47/5.28  
% 12.47/5.28  
% 12.47/5.28  %Foreground operators:
% 12.47/5.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.47/5.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.47/5.28  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 12.47/5.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.47/5.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.47/5.28  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.47/5.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.47/5.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 12.47/5.28  tff(v3_tops_2, type, v3_tops_2: ($i * $i * $i) > $o).
% 12.47/5.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.47/5.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.47/5.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.47/5.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.47/5.28  tff('#skF_5', type, '#skF_5': $i).
% 12.47/5.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.47/5.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.47/5.28  tff('#skF_3', type, '#skF_3': $i).
% 12.47/5.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.47/5.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.47/5.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.47/5.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.47/5.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 12.47/5.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.47/5.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.47/5.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.47/5.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.47/5.28  tff('#skF_4', type, '#skF_4': $i).
% 12.47/5.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.47/5.28  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 12.47/5.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.47/5.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.47/5.28  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 12.47/5.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.47/5.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.47/5.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.47/5.28  
% 12.47/5.30  tff(f_200, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((((v1_compts_1(A) & v8_pre_topc(B)) & (k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A))) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & v5_pre_topc(C, A, B)) => v3_tops_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_compts_1)).
% 12.47/5.30  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.47/5.30  tff(f_98, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 12.47/5.30  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.47/5.30  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.47/5.30  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.47/5.30  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.47/5.30  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.47/5.30  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((~v2_struct_0(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_tops_2(C, A, B) <=> ((((k1_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(A)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v2_funct_1(C)) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) <=> v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_2)).
% 12.47/5.30  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.47/5.30  tff(f_166, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_compts_1(A) & v8_pre_topc(B)) & (k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B))) & v5_pre_topc(C, A, B)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(D, A) => v4_pre_topc(k7_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_compts_1)).
% 12.47/5.30  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 12.47/5.30  tff(f_39, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 12.47/5.30  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 12.47/5.30  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 12.47/5.30  tff(c_60, plain, (~v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.30  tff(c_86, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.30  tff(c_36, plain, (![A_50]: (l1_struct_0(A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.47/5.30  tff(c_90, plain, (![A_93]: (u1_struct_0(A_93)=k2_struct_0(A_93) | ~l1_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.47/5.30  tff(c_95, plain, (![A_94]: (u1_struct_0(A_94)=k2_struct_0(A_94) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_36, c_90])).
% 12.47/5.31  tff(c_103, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_86, c_95])).
% 12.47/5.31  tff(c_80, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_102, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_80, c_95])).
% 12.47/5.31  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_125, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_102, c_74])).
% 12.47/5.31  tff(c_135, plain, (![C_99, A_100, B_101]: (v1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.47/5.31  tff(c_143, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_125, c_135])).
% 12.47/5.31  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_152, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.47/5.31  tff(c_160, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_125, c_152])).
% 12.47/5.31  tff(c_68, plain, (k1_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_130, plain, (k1_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_102, c_68])).
% 12.47/5.31  tff(c_162, plain, (k2_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_130])).
% 12.47/5.31  tff(c_169, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_125])).
% 12.47/5.31  tff(c_14, plain, (![A_15, B_16, C_17]: (k2_relset_1(A_15, B_16, C_17)=k2_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.47/5.31  tff(c_208, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_169, c_14])).
% 12.47/5.31  tff(c_66, plain, (k2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_115, plain, (k2_relset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_102, c_66])).
% 12.47/5.31  tff(c_170, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_115])).
% 12.47/5.31  tff(c_219, plain, (k2_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_170])).
% 12.47/5.31  tff(c_76, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_105, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_76])).
% 12.47/5.31  tff(c_114, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_105])).
% 12.47/5.31  tff(c_171, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_114])).
% 12.47/5.31  tff(c_228, plain, (v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_171])).
% 12.47/5.31  tff(c_225, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_169])).
% 12.47/5.31  tff(c_167, plain, (k1_relset_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4'), '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_160])).
% 12.47/5.31  tff(c_226, plain, (k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_167])).
% 12.47/5.31  tff(c_224, plain, (k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_208])).
% 12.47/5.31  tff(c_64, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_265, plain, (![A_112]: (m1_subset_1(A_112, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_112), k2_relat_1(A_112)))) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.47/5.31  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.47/5.31  tff(c_281, plain, (![A_112]: (r1_tarski(A_112, k2_zfmisc_1(k1_relat_1(A_112), k2_relat_1(A_112))) | ~v1_funct_1(A_112) | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_265, c_2])).
% 12.47/5.31  tff(c_172, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_103])).
% 12.47/5.31  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.47/5.31  tff(c_84, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_229, plain, (u1_struct_0('#skF_4')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_102])).
% 12.47/5.31  tff(c_1814, plain, (![A_356, B_357, C_358]: (m1_subset_1('#skF_2'(A_356, B_357, C_358), k1_zfmisc_1(u1_struct_0(A_356))) | v3_tops_2(C_358, A_356, B_357) | ~v2_funct_1(C_358) | k2_relset_1(u1_struct_0(A_356), u1_struct_0(B_357), C_358)!=k2_struct_0(B_357) | k1_relset_1(u1_struct_0(A_356), u1_struct_0(B_357), C_358)!=k2_struct_0(A_356) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356), u1_struct_0(B_357)))) | ~v1_funct_2(C_358, u1_struct_0(A_356), u1_struct_0(B_357)) | ~v1_funct_1(C_358) | ~l1_pre_topc(B_357) | v2_struct_0(B_357) | ~l1_pre_topc(A_356))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.47/5.31  tff(c_1821, plain, (![A_356, C_358]: (m1_subset_1('#skF_2'(A_356, '#skF_4', C_358), k1_zfmisc_1(u1_struct_0(A_356))) | v3_tops_2(C_358, A_356, '#skF_4') | ~v2_funct_1(C_358) | k2_relset_1(u1_struct_0(A_356), u1_struct_0('#skF_4'), C_358)!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0(A_356), u1_struct_0('#skF_4'), C_358)!=k2_struct_0(A_356) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_358, u1_struct_0(A_356), u1_struct_0('#skF_4')) | ~v1_funct_1(C_358) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_356))), inference(superposition, [status(thm), theory('equality')], [c_229, c_1814])).
% 12.47/5.31  tff(c_1833, plain, (![A_356, C_358]: (m1_subset_1('#skF_2'(A_356, '#skF_4', C_358), k1_zfmisc_1(u1_struct_0(A_356))) | v3_tops_2(C_358, A_356, '#skF_4') | ~v2_funct_1(C_358) | k2_relset_1(u1_struct_0(A_356), k2_relat_1('#skF_5'), C_358)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_356), k2_relat_1('#skF_5'), C_358)!=k2_struct_0(A_356) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_356), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_358, u1_struct_0(A_356), k2_relat_1('#skF_5')) | ~v1_funct_1(C_358) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_356))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_229, c_229, c_229, c_219, c_1821])).
% 12.47/5.31  tff(c_1905, plain, (![A_363, C_364]: (m1_subset_1('#skF_2'(A_363, '#skF_4', C_364), k1_zfmisc_1(u1_struct_0(A_363))) | v3_tops_2(C_364, A_363, '#skF_4') | ~v2_funct_1(C_364) | k2_relset_1(u1_struct_0(A_363), k2_relat_1('#skF_5'), C_364)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_363), k2_relat_1('#skF_5'), C_364)!=k2_struct_0(A_363) | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_363), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_364, u1_struct_0(A_363), k2_relat_1('#skF_5')) | ~v1_funct_1(C_364) | ~l1_pre_topc(A_363))), inference(negUnitSimplification, [status(thm)], [c_84, c_1833])).
% 12.47/5.31  tff(c_2703, plain, (![A_467, A_468]: (m1_subset_1('#skF_2'(A_467, '#skF_4', A_468), k1_zfmisc_1(u1_struct_0(A_467))) | v3_tops_2(A_468, A_467, '#skF_4') | ~v2_funct_1(A_468) | k2_relset_1(u1_struct_0(A_467), k2_relat_1('#skF_5'), A_468)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_467), k2_relat_1('#skF_5'), A_468)!=k2_struct_0(A_467) | ~v1_funct_2(A_468, u1_struct_0(A_467), k2_relat_1('#skF_5')) | ~v1_funct_1(A_468) | ~l1_pre_topc(A_467) | ~r1_tarski(A_468, k2_zfmisc_1(u1_struct_0(A_467), k2_relat_1('#skF_5'))))), inference(resolution, [status(thm)], [c_4, c_1905])).
% 12.47/5.31  tff(c_2713, plain, (![A_468]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', A_468), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v3_tops_2(A_468, '#skF_3', '#skF_4') | ~v2_funct_1(A_468) | k2_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), A_468)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), A_468)!=k2_struct_0('#skF_3') | ~v1_funct_2(A_468, u1_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_468) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_468, k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2703])).
% 12.47/5.31  tff(c_3960, plain, (![A_652]: (m1_subset_1('#skF_2'('#skF_3', '#skF_4', A_652), k1_zfmisc_1(k1_relat_1('#skF_5'))) | v3_tops_2(A_652, '#skF_3', '#skF_4') | ~v2_funct_1(A_652) | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_652)!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_652)!=k1_relat_1('#skF_5') | ~v1_funct_2(A_652, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_652) | ~r1_tarski(A_652, k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_172, c_172, c_162, c_172, c_172, c_2713])).
% 12.47/5.31  tff(c_3976, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k1_relat_1('#skF_5'))) | v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k1_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_281, c_3960])).
% 12.47/5.31  tff(c_3985, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k1_relat_1('#skF_5'))) | v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_78, c_228, c_226, c_224, c_64, c_3976])).
% 12.47/5.31  tff(c_3986, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_3985])).
% 12.47/5.31  tff(c_129, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_125, c_2])).
% 12.47/5.31  tff(c_168, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_129])).
% 12.47/5.31  tff(c_227, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_168])).
% 12.47/5.31  tff(c_62, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_20, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_26), k2_relat_1(A_26)))) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.47/5.31  tff(c_288, plain, (![A_113, B_114, C_115, D_116]: (k7_relset_1(A_113, B_114, C_115, D_116)=k9_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.47/5.31  tff(c_296, plain, (![A_26, D_116]: (k7_relset_1(k1_relat_1(A_26), k2_relat_1(A_26), A_26, D_116)=k9_relat_1(A_26, D_116) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_20, c_288])).
% 12.47/5.31  tff(c_88, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_72, plain, (v1_compts_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_82, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_70, plain, (v8_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 12.47/5.31  tff(c_2003, plain, (![A_373, B_374, C_375, D_376]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_373), u1_struct_0(B_374), C_375, D_376), B_374) | ~v4_pre_topc(D_376, A_373) | ~m1_subset_1(D_376, k1_zfmisc_1(u1_struct_0(A_373))) | ~v5_pre_topc(C_375, A_373, B_374) | k2_relset_1(u1_struct_0(A_373), u1_struct_0(B_374), C_375)!=k2_struct_0(B_374) | ~v8_pre_topc(B_374) | ~v1_compts_1(A_373) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_373), u1_struct_0(B_374)))) | ~v1_funct_2(C_375, u1_struct_0(A_373), u1_struct_0(B_374)) | ~v1_funct_1(C_375) | ~l1_pre_topc(B_374) | ~v2_pre_topc(B_374) | v2_struct_0(B_374) | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373))), inference(cnfTransformation, [status(thm)], [f_166])).
% 12.47/5.31  tff(c_2010, plain, (![A_373, C_375, D_376]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_373), u1_struct_0('#skF_4'), C_375, D_376), '#skF_4') | ~v4_pre_topc(D_376, A_373) | ~m1_subset_1(D_376, k1_zfmisc_1(u1_struct_0(A_373))) | ~v5_pre_topc(C_375, A_373, '#skF_4') | k2_relset_1(u1_struct_0(A_373), u1_struct_0('#skF_4'), C_375)!=k2_struct_0('#skF_4') | ~v8_pre_topc('#skF_4') | ~v1_compts_1(A_373) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_373), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_375, u1_struct_0(A_373), u1_struct_0('#skF_4')) | ~v1_funct_1(C_375) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373))), inference(superposition, [status(thm), theory('equality')], [c_229, c_2003])).
% 12.47/5.31  tff(c_2022, plain, (![A_373, C_375, D_376]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_373), k2_relat_1('#skF_5'), C_375, D_376), '#skF_4') | ~v4_pre_topc(D_376, A_373) | ~m1_subset_1(D_376, k1_zfmisc_1(u1_struct_0(A_373))) | ~v5_pre_topc(C_375, A_373, '#skF_4') | k2_relset_1(u1_struct_0(A_373), k2_relat_1('#skF_5'), C_375)!=k2_relat_1('#skF_5') | ~v1_compts_1(A_373) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_373), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_375, u1_struct_0(A_373), k2_relat_1('#skF_5')) | ~v1_funct_1(C_375) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_229, c_70, c_229, c_219, c_229, c_2010])).
% 12.47/5.31  tff(c_2088, plain, (![A_384, C_385, D_386]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_384), k2_relat_1('#skF_5'), C_385, D_386), '#skF_4') | ~v4_pre_topc(D_386, A_384) | ~m1_subset_1(D_386, k1_zfmisc_1(u1_struct_0(A_384))) | ~v5_pre_topc(C_385, A_384, '#skF_4') | k2_relset_1(u1_struct_0(A_384), k2_relat_1('#skF_5'), C_385)!=k2_relat_1('#skF_5') | ~v1_compts_1(A_384) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_384), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_385, u1_struct_0(A_384), k2_relat_1('#skF_5')) | ~v1_funct_1(C_385) | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384))), inference(negUnitSimplification, [status(thm)], [c_84, c_2022])).
% 12.47/5.31  tff(c_2774, plain, (![A_489, A_490, D_491]: (v4_pre_topc(k7_relset_1(u1_struct_0(A_489), k2_relat_1('#skF_5'), A_490, D_491), '#skF_4') | ~v4_pre_topc(D_491, A_489) | ~m1_subset_1(D_491, k1_zfmisc_1(u1_struct_0(A_489))) | ~v5_pre_topc(A_490, A_489, '#skF_4') | k2_relset_1(u1_struct_0(A_489), k2_relat_1('#skF_5'), A_490)!=k2_relat_1('#skF_5') | ~v1_compts_1(A_489) | ~v1_funct_2(A_490, u1_struct_0(A_489), k2_relat_1('#skF_5')) | ~v1_funct_1(A_490) | ~l1_pre_topc(A_489) | ~v2_pre_topc(A_489) | ~r1_tarski(A_490, k2_zfmisc_1(u1_struct_0(A_489), k2_relat_1('#skF_5'))))), inference(resolution, [status(thm)], [c_4, c_2088])).
% 12.47/5.31  tff(c_2786, plain, (![A_490, D_491]: (v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_490, D_491), '#skF_4') | ~v4_pre_topc(D_491, '#skF_3') | ~m1_subset_1(D_491, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc(A_490, '#skF_3', '#skF_4') | k2_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), A_490)!=k2_relat_1('#skF_5') | ~v1_compts_1('#skF_3') | ~v1_funct_2(A_490, u1_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_490) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski(A_490, k2_zfmisc_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2774])).
% 12.47/5.31  tff(c_3232, plain, (![A_588, D_589]: (v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_588, D_589), '#skF_4') | ~v4_pre_topc(D_589, '#skF_3') | ~m1_subset_1(D_589, k1_zfmisc_1(k1_relat_1('#skF_5'))) | ~v5_pre_topc(A_588, '#skF_3', '#skF_4') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_588)!=k2_relat_1('#skF_5') | ~v1_funct_2(A_588, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_588) | ~r1_tarski(A_588, k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_88, c_86, c_172, c_72, c_172, c_172, c_2786])).
% 12.47/5.31  tff(c_3238, plain, (![D_116]: (v4_pre_topc(k9_relat_1('#skF_5', D_116), '#skF_4') | ~v4_pre_topc(D_116, '#skF_3') | ~m1_subset_1(D_116, k1_zfmisc_1(k1_relat_1('#skF_5'))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_3232])).
% 12.47/5.31  tff(c_3244, plain, (![D_116]: (v4_pre_topc(k9_relat_1('#skF_5', D_116), '#skF_4') | ~v4_pre_topc(D_116, '#skF_3') | ~m1_subset_1(D_116, k1_zfmisc_1(k1_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_78, c_227, c_78, c_228, c_224, c_62, c_3238])).
% 12.47/5.31  tff(c_4044, plain, (v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | ~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_3986, c_3244])).
% 12.47/5.31  tff(c_4052, plain, (~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_4044])).
% 12.47/5.31  tff(c_297, plain, (![D_116]: (k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5', D_116)=k9_relat_1('#skF_5', D_116))), inference(resolution, [status(thm)], [c_225, c_288])).
% 12.47/5.31  tff(c_354, plain, (![A_126, B_127, C_128, D_129]: (m1_subset_1(k7_relset_1(A_126, B_127, C_128, D_129), k1_zfmisc_1(B_127)) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.47/5.31  tff(c_375, plain, (![D_116]: (m1_subset_1(k9_relat_1('#skF_5', D_116), k1_zfmisc_1(k2_relat_1('#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_297, c_354])).
% 12.47/5.31  tff(c_383, plain, (![D_130]: (m1_subset_1(k9_relat_1('#skF_5', D_130), k1_zfmisc_1(k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_375])).
% 12.47/5.31  tff(c_387, plain, (![D_130]: (r1_tarski(k9_relat_1('#skF_5', D_130), k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_383, c_2])).
% 12.47/5.31  tff(c_4045, plain, (r1_tarski('#skF_2'('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3986, c_2])).
% 12.47/5.31  tff(c_6, plain, (![B_4, A_3]: (k10_relat_1(B_4, k9_relat_1(B_4, A_3))=A_3 | ~v2_funct_1(B_4) | ~r1_tarski(A_3, k1_relat_1(B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.47/5.31  tff(c_4047, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4045, c_6])).
% 12.47/5.31  tff(c_4050, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')))='#skF_2'('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_78, c_64, c_4047])).
% 12.47/5.31  tff(c_410, plain, (![A_133, B_134, C_135, D_136]: (k8_relset_1(A_133, B_134, C_135, D_136)=k10_relat_1(C_135, D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.47/5.31  tff(c_422, plain, (![A_26, D_136]: (k8_relset_1(k1_relat_1(A_26), k2_relat_1(A_26), A_26, D_136)=k10_relat_1(A_26, D_136) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_20, c_410])).
% 12.47/5.31  tff(c_1278, plain, (![A_302, B_303, C_304, D_305]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_302), u1_struct_0(B_303), C_304, D_305), A_302) | ~v4_pre_topc(D_305, B_303) | ~m1_subset_1(D_305, k1_zfmisc_1(u1_struct_0(B_303))) | ~v5_pre_topc(C_304, A_302, B_303) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_302), u1_struct_0(B_303)))) | ~v1_funct_2(C_304, u1_struct_0(A_302), u1_struct_0(B_303)) | ~v1_funct_1(C_304) | ~l1_pre_topc(B_303) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_94])).
% 12.47/5.31  tff(c_2505, plain, (![A_435, B_436, A_437, D_438]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_435), u1_struct_0(B_436), A_437, D_438), A_435) | ~v4_pre_topc(D_438, B_436) | ~m1_subset_1(D_438, k1_zfmisc_1(u1_struct_0(B_436))) | ~v5_pre_topc(A_437, A_435, B_436) | ~v1_funct_2(A_437, u1_struct_0(A_435), u1_struct_0(B_436)) | ~v1_funct_1(A_437) | ~l1_pre_topc(B_436) | ~l1_pre_topc(A_435) | ~r1_tarski(A_437, k2_zfmisc_1(u1_struct_0(A_435), u1_struct_0(B_436))))), inference(resolution, [status(thm)], [c_4, c_1278])).
% 12.47/5.31  tff(c_2518, plain, (![B_436, A_437, D_438]: (v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'), u1_struct_0(B_436), A_437, D_438), '#skF_3') | ~v4_pre_topc(D_438, B_436) | ~m1_subset_1(D_438, k1_zfmisc_1(u1_struct_0(B_436))) | ~v5_pre_topc(A_437, '#skF_3', B_436) | ~v1_funct_2(A_437, u1_struct_0('#skF_3'), u1_struct_0(B_436)) | ~v1_funct_1(A_437) | ~l1_pre_topc(B_436) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_437, k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_436))))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2505])).
% 12.47/5.31  tff(c_2648, plain, (![B_461, A_462, D_463]: (v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'), u1_struct_0(B_461), A_462, D_463), '#skF_3') | ~v4_pre_topc(D_463, B_461) | ~m1_subset_1(D_463, k1_zfmisc_1(u1_struct_0(B_461))) | ~v5_pre_topc(A_462, '#skF_3', B_461) | ~v1_funct_2(A_462, k1_relat_1('#skF_5'), u1_struct_0(B_461)) | ~v1_funct_1(A_462) | ~l1_pre_topc(B_461) | ~r1_tarski(A_462, k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0(B_461))))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_86, c_172, c_2518])).
% 12.47/5.31  tff(c_2655, plain, (![A_462, D_463]: (v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_462, D_463), '#skF_3') | ~v4_pre_topc(D_463, '#skF_4') | ~m1_subset_1(D_463, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v5_pre_topc(A_462, '#skF_3', '#skF_4') | ~v1_funct_2(A_462, k1_relat_1('#skF_5'), u1_struct_0('#skF_4')) | ~v1_funct_1(A_462) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_462, k2_zfmisc_1(k1_relat_1('#skF_5'), u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_229, c_2648])).
% 12.47/5.31  tff(c_2664, plain, (![A_464, D_465]: (v4_pre_topc(k8_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), A_464, D_465), '#skF_3') | ~v4_pre_topc(D_465, '#skF_4') | ~m1_subset_1(D_465, k1_zfmisc_1(k2_relat_1('#skF_5'))) | ~v5_pre_topc(A_464, '#skF_3', '#skF_4') | ~v1_funct_2(A_464, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(A_464) | ~r1_tarski(A_464, k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_229, c_80, c_229, c_229, c_2655])).
% 12.47/5.31  tff(c_2672, plain, (![D_136]: (v4_pre_topc(k10_relat_1('#skF_5', D_136), '#skF_3') | ~v4_pre_topc(D_136, '#skF_4') | ~m1_subset_1(D_136, k1_zfmisc_1(k2_relat_1('#skF_5'))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_422, c_2664])).
% 12.47/5.31  tff(c_2681, plain, (![D_466]: (v4_pre_topc(k10_relat_1('#skF_5', D_466), '#skF_3') | ~v4_pre_topc(D_466, '#skF_4') | ~m1_subset_1(D_466, k1_zfmisc_1(k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_78, c_227, c_78, c_228, c_62, c_2672])).
% 12.47/5.31  tff(c_2702, plain, (![A_1]: (v4_pre_topc(k10_relat_1('#skF_5', A_1), '#skF_3') | ~v4_pre_topc(A_1, '#skF_4') | ~r1_tarski(A_1, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_4, c_2681])).
% 12.47/5.31  tff(c_4056, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | ~v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | ~r1_tarski(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), k2_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4050, c_2702])).
% 12.47/5.31  tff(c_4063, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | ~v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_4056])).
% 12.47/5.31  tff(c_4064, plain, (~v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_4052, c_4063])).
% 12.47/5.31  tff(c_2194, plain, (![A_395, B_396, C_397]: (v4_pre_topc('#skF_2'(A_395, B_396, C_397), A_395) | v4_pre_topc(k7_relset_1(u1_struct_0(A_395), u1_struct_0(B_396), C_397, '#skF_2'(A_395, B_396, C_397)), B_396) | v3_tops_2(C_397, A_395, B_396) | ~v2_funct_1(C_397) | k2_relset_1(u1_struct_0(A_395), u1_struct_0(B_396), C_397)!=k2_struct_0(B_396) | k1_relset_1(u1_struct_0(A_395), u1_struct_0(B_396), C_397)!=k2_struct_0(A_395) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), u1_struct_0(B_396)))) | ~v1_funct_2(C_397, u1_struct_0(A_395), u1_struct_0(B_396)) | ~v1_funct_1(C_397) | ~l1_pre_topc(B_396) | v2_struct_0(B_396) | ~l1_pre_topc(A_395))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.47/5.31  tff(c_2202, plain, (![A_395, C_397]: (v4_pre_topc('#skF_2'(A_395, '#skF_4', C_397), A_395) | v4_pre_topc(k7_relset_1(u1_struct_0(A_395), k2_relat_1('#skF_5'), C_397, '#skF_2'(A_395, '#skF_4', C_397)), '#skF_4') | v3_tops_2(C_397, A_395, '#skF_4') | ~v2_funct_1(C_397) | k2_relset_1(u1_struct_0(A_395), u1_struct_0('#skF_4'), C_397)!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0(A_395), u1_struct_0('#skF_4'), C_397)!=k2_struct_0(A_395) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_397, u1_struct_0(A_395), u1_struct_0('#skF_4')) | ~v1_funct_1(C_397) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_395))), inference(superposition, [status(thm), theory('equality')], [c_229, c_2194])).
% 12.47/5.31  tff(c_2213, plain, (![A_395, C_397]: (v4_pre_topc('#skF_2'(A_395, '#skF_4', C_397), A_395) | v4_pre_topc(k7_relset_1(u1_struct_0(A_395), k2_relat_1('#skF_5'), C_397, '#skF_2'(A_395, '#skF_4', C_397)), '#skF_4') | v3_tops_2(C_397, A_395, '#skF_4') | ~v2_funct_1(C_397) | k2_relset_1(u1_struct_0(A_395), k2_relat_1('#skF_5'), C_397)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_395), k2_relat_1('#skF_5'), C_397)!=k2_struct_0(A_395) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_397, u1_struct_0(A_395), k2_relat_1('#skF_5')) | ~v1_funct_1(C_397) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_395))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_229, c_229, c_229, c_229, c_219, c_2202])).
% 12.47/5.31  tff(c_2285, plain, (![A_404, C_405]: (v4_pre_topc('#skF_2'(A_404, '#skF_4', C_405), A_404) | v4_pre_topc(k7_relset_1(u1_struct_0(A_404), k2_relat_1('#skF_5'), C_405, '#skF_2'(A_404, '#skF_4', C_405)), '#skF_4') | v3_tops_2(C_405, A_404, '#skF_4') | ~v2_funct_1(C_405) | k2_relset_1(u1_struct_0(A_404), k2_relat_1('#skF_5'), C_405)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_404), k2_relat_1('#skF_5'), C_405)!=k2_struct_0(A_404) | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_404), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_405, u1_struct_0(A_404), k2_relat_1('#skF_5')) | ~v1_funct_1(C_405) | ~l1_pre_topc(A_404))), inference(negUnitSimplification, [status(thm)], [c_84, c_2213])).
% 12.47/5.31  tff(c_2293, plain, (![C_405]: (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', C_405), '#skF_3') | v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_405, '#skF_2'('#skF_3', '#skF_4', C_405)), '#skF_4') | v3_tops_2(C_405, '#skF_3', '#skF_4') | ~v2_funct_1(C_405) | k2_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), C_405)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), C_405)!=k2_struct_0('#skF_3') | ~m1_subset_1(C_405, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_405, u1_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1(C_405) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2285])).
% 12.47/5.31  tff(c_8916, plain, (![C_979]: (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', C_979), '#skF_3') | v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_979, '#skF_2'('#skF_3', '#skF_4', C_979)), '#skF_4') | v3_tops_2(C_979, '#skF_3', '#skF_4') | ~v2_funct_1(C_979) | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_979)!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_979)!=k1_relat_1('#skF_5') | ~m1_subset_1(C_979, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_979, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(C_979))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_172, c_172, c_172, c_162, c_172, c_2293])).
% 12.47/5.31  tff(c_8930, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k1_relat_1('#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_296, c_8916])).
% 12.47/5.31  tff(c_8937, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_78, c_78, c_228, c_225, c_226, c_224, c_64, c_8930])).
% 12.47/5.31  tff(c_8939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_4064, c_4052, c_8937])).
% 12.47/5.31  tff(c_8941, plain, (v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_4044])).
% 12.47/5.31  tff(c_8940, plain, (v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitRight, [status(thm)], [c_4044])).
% 12.47/5.31  tff(c_2397, plain, (![A_417, B_418, C_419]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_417), u1_struct_0(B_418), C_419, '#skF_2'(A_417, B_418, C_419)), B_418) | ~v4_pre_topc('#skF_2'(A_417, B_418, C_419), A_417) | v3_tops_2(C_419, A_417, B_418) | ~v2_funct_1(C_419) | k2_relset_1(u1_struct_0(A_417), u1_struct_0(B_418), C_419)!=k2_struct_0(B_418) | k1_relset_1(u1_struct_0(A_417), u1_struct_0(B_418), C_419)!=k2_struct_0(A_417) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417), u1_struct_0(B_418)))) | ~v1_funct_2(C_419, u1_struct_0(A_417), u1_struct_0(B_418)) | ~v1_funct_1(C_419) | ~l1_pre_topc(B_418) | v2_struct_0(B_418) | ~l1_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_132])).
% 12.47/5.31  tff(c_2406, plain, (![A_417, C_419]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_417), k2_relat_1('#skF_5'), C_419, '#skF_2'(A_417, '#skF_4', C_419)), '#skF_4') | ~v4_pre_topc('#skF_2'(A_417, '#skF_4', C_419), A_417) | v3_tops_2(C_419, A_417, '#skF_4') | ~v2_funct_1(C_419) | k2_relset_1(u1_struct_0(A_417), u1_struct_0('#skF_4'), C_419)!=k2_struct_0('#skF_4') | k1_relset_1(u1_struct_0(A_417), u1_struct_0('#skF_4'), C_419)!=k2_struct_0(A_417) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417), u1_struct_0('#skF_4')))) | ~v1_funct_2(C_419, u1_struct_0(A_417), u1_struct_0('#skF_4')) | ~v1_funct_1(C_419) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_417))), inference(superposition, [status(thm), theory('equality')], [c_229, c_2397])).
% 12.47/5.31  tff(c_2417, plain, (![A_417, C_419]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_417), k2_relat_1('#skF_5'), C_419, '#skF_2'(A_417, '#skF_4', C_419)), '#skF_4') | ~v4_pre_topc('#skF_2'(A_417, '#skF_4', C_419), A_417) | v3_tops_2(C_419, A_417, '#skF_4') | ~v2_funct_1(C_419) | k2_relset_1(u1_struct_0(A_417), k2_relat_1('#skF_5'), C_419)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_417), k2_relat_1('#skF_5'), C_419)!=k2_struct_0(A_417) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_417), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_419, u1_struct_0(A_417), k2_relat_1('#skF_5')) | ~v1_funct_1(C_419) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_417))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_229, c_229, c_229, c_229, c_219, c_2406])).
% 12.47/5.31  tff(c_2448, plain, (![A_424, C_425]: (~v4_pre_topc(k7_relset_1(u1_struct_0(A_424), k2_relat_1('#skF_5'), C_425, '#skF_2'(A_424, '#skF_4', C_425)), '#skF_4') | ~v4_pre_topc('#skF_2'(A_424, '#skF_4', C_425), A_424) | v3_tops_2(C_425, A_424, '#skF_4') | ~v2_funct_1(C_425) | k2_relset_1(u1_struct_0(A_424), k2_relat_1('#skF_5'), C_425)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0(A_424), k2_relat_1('#skF_5'), C_425)!=k2_struct_0(A_424) | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_424), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_425, u1_struct_0(A_424), k2_relat_1('#skF_5')) | ~v1_funct_1(C_425) | ~l1_pre_topc(A_424))), inference(negUnitSimplification, [status(thm)], [c_84, c_2417])).
% 12.47/5.31  tff(c_2457, plain, (![C_425]: (~v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_425, '#skF_2'('#skF_3', '#skF_4', C_425)), '#skF_4') | ~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', C_425), '#skF_3') | v3_tops_2(C_425, '#skF_3', '#skF_4') | ~v2_funct_1(C_425) | k2_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), C_425)!=k2_relat_1('#skF_5') | k1_relset_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5'), C_425)!=k2_struct_0('#skF_3') | ~m1_subset_1(C_425, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_425, u1_struct_0('#skF_3'), k2_relat_1('#skF_5')) | ~v1_funct_1(C_425) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_2448])).
% 12.47/5.31  tff(c_13866, plain, (![C_1307]: (~v4_pre_topc(k7_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1307, '#skF_2'('#skF_3', '#skF_4', C_1307)), '#skF_4') | ~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', C_1307), '#skF_3') | v3_tops_2(C_1307, '#skF_3', '#skF_4') | ~v2_funct_1(C_1307) | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1307)!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), C_1307)!=k1_relat_1('#skF_5') | ~m1_subset_1(C_1307, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2(C_1307, k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1(C_1307))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_172, c_172, c_172, c_162, c_172, c_2457])).
% 12.47/5.31  tff(c_13889, plain, (~v4_pre_topc(k9_relat_1('#skF_5', '#skF_2'('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | ~v4_pre_topc('#skF_2'('#skF_3', '#skF_4', '#skF_5'), '#skF_3') | v3_tops_2('#skF_5', '#skF_3', '#skF_4') | ~v2_funct_1('#skF_5') | k2_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k2_relat_1('#skF_5') | k1_relset_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5'), '#skF_5')!=k1_relat_1('#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), k2_relat_1('#skF_5')))) | ~v1_funct_2('#skF_5', k1_relat_1('#skF_5'), k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_296, c_13866])).
% 12.47/5.31  tff(c_13898, plain, (v3_tops_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_78, c_78, c_228, c_225, c_226, c_224, c_64, c_8941, c_8940, c_13889])).
% 12.47/5.31  tff(c_13900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_13898])).
% 12.47/5.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.47/5.31  
% 12.47/5.31  Inference rules
% 12.47/5.31  ----------------------
% 12.47/5.31  #Ref     : 0
% 12.47/5.31  #Sup     : 3016
% 12.47/5.31  #Fact    : 0
% 12.47/5.31  #Define  : 0
% 12.47/5.31  #Split   : 4
% 12.47/5.31  #Chain   : 0
% 12.47/5.31  #Close   : 0
% 12.47/5.31  
% 12.47/5.31  Ordering : KBO
% 12.47/5.31  
% 12.47/5.31  Simplification rules
% 12.47/5.31  ----------------------
% 12.47/5.31  #Subsume      : 269
% 12.47/5.31  #Demod        : 3272
% 12.47/5.31  #Tautology    : 248
% 12.47/5.31  #SimpNegUnit  : 79
% 12.47/5.31  #BackRed      : 15
% 12.47/5.31  
% 12.47/5.31  #Partial instantiations: 0
% 12.47/5.31  #Strategies tried      : 1
% 12.47/5.31  
% 12.47/5.31  Timing (in seconds)
% 12.47/5.31  ----------------------
% 12.47/5.31  Preprocessing        : 0.47
% 12.47/5.31  Parsing              : 0.24
% 12.47/5.31  CNF conversion       : 0.04
% 12.47/5.31  Main loop            : 4.00
% 12.47/5.31  Inferencing          : 1.27
% 12.47/5.31  Reduction            : 1.39
% 12.47/5.31  Demodulation         : 1.08
% 12.47/5.31  BG Simplification    : 0.21
% 12.47/5.31  Subsumption          : 0.84
% 12.47/5.31  Abstraction          : 0.32
% 12.47/5.31  MUC search           : 0.00
% 12.47/5.31  Cooper               : 0.00
% 12.47/5.31  Total                : 4.53
% 12.47/5.31  Index Insertion      : 0.00
% 12.47/5.31  Index Deletion       : 0.00
% 12.47/5.31  Index Matching       : 0.00
% 12.47/5.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
