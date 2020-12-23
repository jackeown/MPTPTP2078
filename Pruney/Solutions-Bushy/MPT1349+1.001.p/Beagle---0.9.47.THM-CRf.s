%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1349+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:50 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  221 (2254 expanded)
%              Number of leaves         :   45 ( 880 expanded)
%              Depth                    :   16
%              Number of atoms          :  641 (12676 expanded)
%              Number of equality atoms :   79 (2384 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_tops_2 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v2_funct_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k7_relset_1 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k2_pre_topc > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_158,axiom,(
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

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_54,axiom,(
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

tff(f_111,axiom,(
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

tff(f_137,axiom,(
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

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2712,plain,(
    ! [A_414,B_415,C_416] :
      ( k2_relset_1(A_414,B_415,C_416) = k2_relat_1(C_416)
      | ~ m1_subset_1(C_416,k1_zfmisc_1(k2_zfmisc_1(A_414,B_415))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2716,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2712])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_72,plain,(
    ! [D_104] :
      ( v3_tops_2('#skF_5','#skF_3','#skF_4')
      | k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3',D_104)) = k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_104))
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_126,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_90,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_125,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_111,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_115,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_111])).

tff(c_84,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_106,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_116,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_106])).

tff(c_78,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_98,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_145,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k7_relset_1(A_119,B_120,C_121,D_122) = k9_relat_1(C_121,D_122)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_148,plain,(
    ! [D_122] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_122) = k9_relat_1('#skF_5',D_122) ),
    inference(resolution,[status(thm)],[c_50,c_145])).

tff(c_68,plain,
    ( k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3','#skF_6')) != k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_6'))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_244,plain,(
    k9_relat_1('#skF_5',k2_pre_topc('#skF_3','#skF_6')) != k2_pre_topc('#skF_4',k9_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_125,c_116,c_115,c_98,c_148,c_148,c_68])).

tff(c_70,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_166,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_125,c_116,c_115,c_98,c_70])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k2_pre_topc(A_10,B_11),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_28,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_703,plain,(
    ! [B_194,A_195,C_196,D_197] :
      ( k8_relset_1(u1_struct_0(B_194),u1_struct_0(A_195),k2_tops_2(u1_struct_0(A_195),u1_struct_0(B_194),C_196),D_197) = k7_relset_1(u1_struct_0(A_195),u1_struct_0(B_194),C_196,D_197)
      | ~ v2_funct_1(C_196)
      | k2_relset_1(u1_struct_0(A_195),u1_struct_0(B_194),C_196) != k2_struct_0(B_194)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_195),u1_struct_0(B_194))))
      | ~ v1_funct_2(C_196,u1_struct_0(A_195),u1_struct_0(B_194))
      | ~ v1_funct_1(C_196)
      | ~ l1_struct_0(B_194)
      | ~ l1_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_173,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_subset_1(k2_tops_2(A_130,B_131,C_132),k1_zfmisc_1(k2_zfmisc_1(B_131,A_130)))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_2(C_132,A_130,B_131)
      | ~ v1_funct_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k8_relset_1(A_23,B_24,C_25,D_26) = k10_relat_1(C_25,D_26)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_216,plain,(
    ! [B_139,A_140,C_141,D_142] :
      ( k8_relset_1(B_139,A_140,k2_tops_2(A_140,B_139,C_141),D_142) = k10_relat_1(k2_tops_2(A_140,B_139,C_141),D_142)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139)))
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ v1_funct_1(C_141) ) ),
    inference(resolution,[status(thm)],[c_173,c_34])).

tff(c_220,plain,(
    ! [D_142] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_142) = k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_142)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_216])).

tff(c_224,plain,(
    ! [D_142] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_142) = k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_220])).

tff(c_729,plain,(
    ! [D_197] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_197) = k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_197)
      | ~ v2_funct_1('#skF_5')
      | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
      | ~ m1_subset_1(D_197,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_224])).

tff(c_743,plain,(
    ! [D_197] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_197) = k9_relat_1('#skF_5',D_197)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_115,c_116,c_98,c_148,c_729])).

tff(c_749,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_743])).

tff(c_752,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_749])).

tff(c_756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_752])).

tff(c_757,plain,(
    ! [D_197] :
      ( ~ l1_struct_0('#skF_4')
      | k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_197) = k9_relat_1('#skF_5',D_197)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_743])).

tff(c_760,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_757])).

tff(c_763,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_760])).

tff(c_767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_763])).

tff(c_768,plain,(
    ! [D_197] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_197) = k9_relat_1('#skF_5',D_197)
      | ~ m1_subset_1(D_197,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_757])).

tff(c_770,plain,(
    ! [D_198] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_198) = k9_relat_1('#skF_5',D_198)
      | ~ m1_subset_1(D_198,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_757])).

tff(c_22,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k2_tops_2(A_12,B_13,C_14),k1_zfmisc_1(k2_zfmisc_1(B_13,A_12)))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_158,plain,(
    ! [A_124,B_125,C_126] :
      ( v1_funct_1(k2_tops_2(A_124,B_125,C_126))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_2(C_126,A_124,B_125)
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_161,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_158])).

tff(c_164,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_161])).

tff(c_167,plain,(
    ! [A_127,B_128,C_129] :
      ( v1_funct_2(k2_tops_2(A_127,B_128,C_129),B_128,A_127)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_2(C_129,A_127,B_128)
      | ~ v1_funct_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_169,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_167])).

tff(c_172,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_169])).

tff(c_290,plain,(
    ! [A_158,B_159,C_160] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(A_158),u1_struct_0(B_159),C_160),B_159,A_158)
      | ~ v3_tops_2(C_160,A_158,B_159)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_158),u1_struct_0(B_159))))
      | ~ v1_funct_2(C_160,u1_struct_0(A_158),u1_struct_0(B_159))
      | ~ v1_funct_1(C_160)
      | ~ l1_pre_topc(B_159)
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_295,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_290])).

tff(c_299,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_52,c_126,c_295])).

tff(c_346,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( r1_tarski(k2_pre_topc(A_176,k8_relset_1(u1_struct_0(A_176),u1_struct_0(B_177),C_178,D_179)),k8_relset_1(u1_struct_0(A_176),u1_struct_0(B_177),C_178,k2_pre_topc(B_177,D_179)))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0(B_177)))
      | ~ v5_pre_topc(C_178,A_176,B_177)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_176),u1_struct_0(B_177))))
      | ~ v1_funct_2(C_178,u1_struct_0(A_176),u1_struct_0(B_177))
      | ~ v1_funct_1(C_178)
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_351,plain,(
    ! [D_142] :
      ( r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_142)),k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_142)))
      | ~ m1_subset_1(D_142,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_346])).

tff(c_365,plain,(
    ! [D_142] :
      ( r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_142)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_142)))
      | ~ m1_subset_1(D_142,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_164,c_172,c_299,c_224,c_351])).

tff(c_379,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_382,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_379])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_382])).

tff(c_388,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_355,plain,(
    ! [D_179] :
      ( r1_tarski(k2_pre_topc('#skF_4',k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_179)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_179)))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_346])).

tff(c_367,plain,(
    ! [D_179] :
      ( r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_179)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_179)))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_164,c_172,c_299,c_224,c_355])).

tff(c_509,plain,(
    ! [D_179] :
      ( r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_179)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_179)))
      | ~ m1_subset_1(D_179,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_367])).

tff(c_799,plain,(
    ! [D_202] :
      ( r1_tarski(k2_pre_topc('#skF_4',k9_relat_1('#skF_5',D_202)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_202)))
      | ~ m1_subset_1(D_202,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_202,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_770,c_509])).

tff(c_821,plain,(
    ! [D_205] :
      ( r1_tarski(k2_pre_topc('#skF_4',k9_relat_1('#skF_5',D_205)),k9_relat_1('#skF_5',k2_pre_topc('#skF_3',D_205)))
      | ~ m1_subset_1(D_205,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(D_205,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k2_pre_topc('#skF_3',D_205),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_799])).

tff(c_254,plain,(
    ! [C_149,A_150,B_151] :
      ( v5_pre_topc(C_149,A_150,B_151)
      | ~ v3_tops_2(C_149,A_150,B_151)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_150),u1_struct_0(B_151))))
      | ~ v1_funct_2(C_149,u1_struct_0(A_150),u1_struct_0(B_151))
      | ~ v1_funct_1(C_149)
      | ~ l1_pre_topc(B_151)
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_261,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_254])).

tff(c_265,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_52,c_126,c_261])).

tff(c_557,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( r1_tarski(k7_relset_1(u1_struct_0(A_188),u1_struct_0(B_189),C_190,k2_pre_topc(A_188,D_191)),k2_pre_topc(B_189,k7_relset_1(u1_struct_0(A_188),u1_struct_0(B_189),C_190,D_191)))
      | ~ m1_subset_1(D_191,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ v5_pre_topc(C_190,A_188,B_189)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_188),u1_struct_0(B_189))))
      | ~ v1_funct_2(C_190,u1_struct_0(A_188),u1_struct_0(B_189))
      | ~ v1_funct_1(C_190)
      | ~ l1_pre_topc(B_189)
      | ~ v2_pre_topc(B_189)
      | v2_struct_0(B_189)
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_577,plain,(
    ! [D_191] :
      ( r1_tarski(k9_relat_1('#skF_5',k2_pre_topc('#skF_3',D_191)),k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_191)))
      | ~ m1_subset_1(D_191,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_557])).

tff(c_593,plain,(
    ! [D_191] :
      ( r1_tarski(k9_relat_1('#skF_5',k2_pre_topc('#skF_3',D_191)),k2_pre_topc('#skF_4',k9_relat_1('#skF_5',D_191)))
      | ~ m1_subset_1(D_191,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_50,c_265,c_148,c_577])).

tff(c_598,plain,(
    ! [D_192] :
      ( r1_tarski(k9_relat_1('#skF_5',k2_pre_topc('#skF_3',D_192)),k2_pre_topc('#skF_4',k9_relat_1('#skF_5',D_192)))
      | ~ m1_subset_1(D_192,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_593])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_601,plain,(
    ! [D_192] :
      ( k9_relat_1('#skF_5',k2_pre_topc('#skF_3',D_192)) = k2_pre_topc('#skF_4',k9_relat_1('#skF_5',D_192))
      | ~ r1_tarski(k2_pre_topc('#skF_4',k9_relat_1('#skF_5',D_192)),k9_relat_1('#skF_5',k2_pre_topc('#skF_3',D_192)))
      | ~ m1_subset_1(D_192,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_598,c_2])).

tff(c_829,plain,(
    ! [D_206] :
      ( k9_relat_1('#skF_5',k2_pre_topc('#skF_3',D_206)) = k2_pre_topc('#skF_4',k9_relat_1('#skF_5',D_206))
      | ~ m1_subset_1(D_206,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k2_pre_topc('#skF_3',D_206),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_821,c_601])).

tff(c_833,plain,(
    ! [B_11] :
      ( k9_relat_1('#skF_5',k2_pre_topc('#skF_3',B_11)) = k2_pre_topc('#skF_4',k9_relat_1('#skF_5',B_11))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_829])).

tff(c_883,plain,(
    ! [B_210] :
      ( k9_relat_1('#skF_5',k2_pre_topc('#skF_3',B_210)) = k2_pre_topc('#skF_4',k9_relat_1('#skF_5',B_210))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_833])).

tff(c_886,plain,(
    k9_relat_1('#skF_5',k2_pre_topc('#skF_3','#skF_6')) = k2_pre_topc('#skF_4',k9_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_166,c_883])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_886])).

tff(c_896,plain,(
    ~ v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1110,plain,(
    ! [A_269,B_270,C_271] :
      ( m1_subset_1('#skF_1'(A_269,B_270,C_271),k1_zfmisc_1(u1_struct_0(B_270)))
      | v5_pre_topc(C_271,A_269,B_270)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_269),u1_struct_0(B_270))))
      | ~ v1_funct_2(C_271,u1_struct_0(A_269),u1_struct_0(B_270))
      | ~ v1_funct_1(C_271)
      | ~ l1_pre_topc(B_270)
      | ~ v2_pre_topc(B_270)
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1115,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1110])).

tff(c_1119,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_1115])).

tff(c_1120,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1119])).

tff(c_930,plain,(
    ! [A_223,B_224,C_225] :
      ( v1_funct_1(k2_tops_2(A_223,B_224,C_225))
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_2(C_225,A_223,B_224)
      | ~ v1_funct_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_933,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_930])).

tff(c_936,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_933])).

tff(c_937,plain,(
    ! [A_226,B_227,C_228] :
      ( v1_funct_2(k2_tops_2(A_226,B_227,C_228),B_227,A_226)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_2(C_228,A_226,B_227)
      | ~ v1_funct_1(C_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_939,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_937])).

tff(c_942,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_939])).

tff(c_945,plain,(
    ! [A_229,B_230,C_231] :
      ( m1_subset_1(k2_tops_2(A_229,B_230,C_231),k1_zfmisc_1(k2_zfmisc_1(B_230,A_229)))
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_2(C_231,A_229,B_230)
      | ~ v1_funct_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1034,plain,(
    ! [B_246,A_247,C_248,D_249] :
      ( k8_relset_1(B_246,A_247,k2_tops_2(A_247,B_246,C_248),D_249) = k10_relat_1(k2_tops_2(A_247,B_246,C_248),D_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246)))
      | ~ v1_funct_2(C_248,A_247,B_246)
      | ~ v1_funct_1(C_248) ) ),
    inference(resolution,[status(thm)],[c_945,c_34])).

tff(c_1038,plain,(
    ! [D_249] :
      ( k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249) = k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_1034])).

tff(c_1042,plain,(
    ! [D_249] : k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249) = k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1038])).

tff(c_1141,plain,(
    ! [A_278,B_279,C_280,D_281] :
      ( r1_tarski(k2_pre_topc(A_278,k8_relset_1(u1_struct_0(A_278),u1_struct_0(B_279),C_280,D_281)),k8_relset_1(u1_struct_0(A_278),u1_struct_0(B_279),C_280,k2_pre_topc(B_279,D_281)))
      | ~ m1_subset_1(D_281,k1_zfmisc_1(u1_struct_0(B_279)))
      | ~ v5_pre_topc(C_280,A_278,B_279)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_278),u1_struct_0(B_279))))
      | ~ v1_funct_2(C_280,u1_struct_0(A_278),u1_struct_0(B_279))
      | ~ v1_funct_1(C_280)
      | ~ l1_pre_topc(B_279)
      | ~ v2_pre_topc(B_279)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1146,plain,(
    ! [D_249] :
      ( r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249)),k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_249)))
      | ~ m1_subset_1(D_249,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_1141])).

tff(c_1160,plain,(
    ! [D_249] :
      ( r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_249)))
      | ~ m1_subset_1(D_249,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_936,c_942,c_1042,c_1146])).

tff(c_1223,plain,(
    ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1160])).

tff(c_1268,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1223])).

tff(c_1272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1268])).

tff(c_1274,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_1160])).

tff(c_1150,plain,(
    ! [D_281] :
      ( r1_tarski(k2_pre_topc('#skF_4',k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_281)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_281)))
      | ~ m1_subset_1(D_281,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_1141])).

tff(c_1162,plain,(
    ! [D_281] :
      ( r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_281)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_281)))
      | ~ m1_subset_1(D_281,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
      | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_936,c_942,c_1042,c_1150])).

tff(c_1375,plain,(
    ! [D_281] :
      ( r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_281)),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3',D_281)))
      | ~ m1_subset_1(D_281,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1274,c_1162])).

tff(c_1376,plain,(
    ~ v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1375])).

tff(c_40,plain,(
    ! [A_27,B_39,C_45] :
      ( m1_subset_1('#skF_1'(A_27,B_39,C_45),k1_zfmisc_1(u1_struct_0(B_39)))
      | v5_pre_topc(C_45,A_27,B_39)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_27),u1_struct_0(B_39))))
      | ~ v1_funct_2(C_45,u1_struct_0(A_27),u1_struct_0(B_39))
      | ~ v1_funct_1(C_45)
      | ~ l1_pre_topc(B_39)
      | ~ v2_pre_topc(B_39)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1284,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1274,c_40])).

tff(c_1333,plain,
    ( m1_subset_1('#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_936,c_942,c_1284])).

tff(c_1422,plain,(
    m1_subset_1('#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1376,c_1333])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_904,plain,(
    ! [A_213,B_214,C_215,D_216] :
      ( k7_relset_1(A_213,B_214,C_215,D_216) = k9_relat_1(C_215,D_216)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_907,plain,(
    ! [D_216] : k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_216) = k9_relat_1('#skF_5',D_216) ),
    inference(resolution,[status(thm)],[c_50,c_904])).

tff(c_895,plain,(
    ! [D_104] :
      ( k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_3',D_104)) = k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_104))
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_963,plain,(
    ! [D_104] :
      ( k9_relat_1('#skF_5',k2_pre_topc('#skF_3',D_104)) = k2_pre_topc('#skF_4',k9_relat_1('#skF_5',D_104))
      | ~ m1_subset_1(D_104,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_907,c_895])).

tff(c_1430,plain,(
    k9_relat_1('#skF_5',k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))) = k2_pre_topc('#skF_4',k9_relat_1('#skF_5','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))) ),
    inference(resolution,[status(thm)],[c_1422,c_963])).

tff(c_1444,plain,(
    ! [B_300,A_301,C_302,D_303] :
      ( k8_relset_1(u1_struct_0(B_300),u1_struct_0(A_301),k2_tops_2(u1_struct_0(A_301),u1_struct_0(B_300),C_302),D_303) = k7_relset_1(u1_struct_0(A_301),u1_struct_0(B_300),C_302,D_303)
      | ~ v2_funct_1(C_302)
      | k2_relset_1(u1_struct_0(A_301),u1_struct_0(B_300),C_302) != k2_struct_0(B_300)
      | ~ m1_subset_1(D_303,k1_zfmisc_1(u1_struct_0(A_301)))
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_301),u1_struct_0(B_300))))
      | ~ v1_funct_2(C_302,u1_struct_0(A_301),u1_struct_0(B_300))
      | ~ v1_funct_1(C_302)
      | ~ l1_struct_0(B_300)
      | ~ l1_struct_0(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1470,plain,(
    ! [D_303] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_303) = k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_303)
      | ~ v2_funct_1('#skF_5')
      | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
      | ~ m1_subset_1(D_303,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1444,c_1042])).

tff(c_1484,plain,(
    ! [D_303] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_303) = k9_relat_1('#skF_5',D_303)
      | ~ m1_subset_1(D_303,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_115,c_116,c_98,c_907,c_1470])).

tff(c_1490,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1484])).

tff(c_1493,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1490])).

tff(c_1497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1493])).

tff(c_1499,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1484])).

tff(c_1479,plain,(
    ! [D_249] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249) = k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_249)
      | ~ v2_funct_1('#skF_5')
      | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
      | ~ m1_subset_1(D_249,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_1444])).

tff(c_1489,plain,(
    ! [D_249] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249) = k9_relat_1('#skF_5',D_249)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_115,c_116,c_98,c_907,c_1479])).

tff(c_1501,plain,(
    ! [D_249] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249) = k9_relat_1('#skF_5',D_249)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_1489])).

tff(c_1502,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1501])).

tff(c_1505,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_1502])).

tff(c_1509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1505])).

tff(c_1510,plain,(
    ! [D_249] :
      ( k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),D_249) = k9_relat_1('#skF_5',D_249)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_1501])).

tff(c_1378,plain,(
    ! [A_297,B_298,C_299] :
      ( ~ r1_tarski(k2_pre_topc(A_297,k8_relset_1(u1_struct_0(A_297),u1_struct_0(B_298),C_299,'#skF_1'(A_297,B_298,C_299))),k8_relset_1(u1_struct_0(A_297),u1_struct_0(B_298),C_299,k2_pre_topc(B_298,'#skF_1'(A_297,B_298,C_299))))
      | v5_pre_topc(C_299,A_297,B_298)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_297),u1_struct_0(B_298))))
      | ~ v1_funct_2(C_299,u1_struct_0(A_297),u1_struct_0(B_298))
      | ~ v1_funct_1(C_299)
      | ~ l1_pre_topc(B_298)
      | ~ v2_pre_topc(B_298)
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1398,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_4',k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_1378])).

tff(c_1416,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))))
    | v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_64,c_62,c_936,c_942,c_1274,c_1042,c_1398])).

tff(c_1417,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_4',k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))))) ),
    inference(negUnitSimplification,[status(thm)],[c_1376,c_1416])).

tff(c_1525,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_4',k9_relat_1('#skF_5','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))))
    | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_1417])).

tff(c_1530,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_4',k9_relat_1('#skF_5','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k10_relat_1(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_1525])).

tff(c_1602,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_4',k9_relat_1('#skF_5','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))),k9_relat_1('#skF_5',k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')))))
    | ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1510,c_1530])).

tff(c_1604,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3','#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1430,c_1602])).

tff(c_1608,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_4','#skF_3',k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1604])).

tff(c_1612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1422,c_1608])).

tff(c_1614,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1375])).

tff(c_1996,plain,(
    ! [C_331,A_332,B_333] :
      ( v3_tops_2(C_331,A_332,B_333)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(A_332),u1_struct_0(B_333),C_331),B_333,A_332)
      | ~ v5_pre_topc(C_331,A_332,B_333)
      | ~ v2_funct_1(C_331)
      | k2_relset_1(u1_struct_0(A_332),u1_struct_0(B_333),C_331) != k2_struct_0(B_333)
      | k1_relset_1(u1_struct_0(A_332),u1_struct_0(B_333),C_331) != k2_struct_0(A_332)
      | ~ m1_subset_1(C_331,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_332),u1_struct_0(B_333))))
      | ~ v1_funct_2(C_331,u1_struct_0(A_332),u1_struct_0(B_333))
      | ~ v1_funct_1(C_331)
      | ~ l1_pre_topc(B_333)
      | ~ l1_pre_topc(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2000,plain,
    ( v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4')
    | k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1614,c_1996])).

tff(c_2007,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_52,c_50,c_125,c_115,c_116,c_98,c_1120,c_2000])).

tff(c_2009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_896,c_2007])).

tff(c_2011,plain,(
    ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1119])).

tff(c_2012,plain,(
    ! [A_334,B_335,C_336] :
      ( m1_subset_1('#skF_2'(A_334,B_335,C_336),k1_zfmisc_1(u1_struct_0(A_334)))
      | v5_pre_topc(C_336,A_334,B_335)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_334),u1_struct_0(B_335))))
      | ~ v1_funct_2(C_336,u1_struct_0(A_334),u1_struct_0(B_335))
      | ~ v1_funct_1(C_336)
      | ~ l1_pre_topc(B_335)
      | ~ v2_pre_topc(B_335)
      | v2_struct_0(B_335)
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2017,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2012])).

tff(c_2021,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_2017])).

tff(c_2022,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2011,c_2021])).

tff(c_2030,plain,(
    k9_relat_1('#skF_5',k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))) = k2_pre_topc('#skF_4',k9_relat_1('#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_2022,c_963])).

tff(c_2501,plain,(
    ! [A_365,B_366,C_367] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_365),u1_struct_0(B_366),C_367,k2_pre_topc(A_365,'#skF_2'(A_365,B_366,C_367))),k2_pre_topc(B_366,k7_relset_1(u1_struct_0(A_365),u1_struct_0(B_366),C_367,'#skF_2'(A_365,B_366,C_367))))
      | v5_pre_topc(C_367,A_365,B_366)
      | ~ m1_subset_1(C_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_365),u1_struct_0(B_366))))
      | ~ v1_funct_2(C_367,u1_struct_0(A_365),u1_struct_0(B_366))
      | ~ v1_funct_1(C_367)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2525,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5',k2_pre_topc('#skF_3','#skF_2'('#skF_3','#skF_4','#skF_5'))),k2_pre_topc('#skF_4',k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_3','#skF_4','#skF_5'))))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_2501])).

tff(c_2542,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_54,c_52,c_50,c_6,c_907,c_2030,c_2525])).

tff(c_2544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2011,c_2542])).

tff(c_2546,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2545,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2695,plain,(
    ! [A_411,B_412,C_413] :
      ( k1_relset_1(u1_struct_0(A_411),u1_struct_0(B_412),C_413) = k2_struct_0(A_411)
      | ~ v3_tops_2(C_413,A_411,B_412)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_411),u1_struct_0(B_412))))
      | ~ v1_funct_2(C_413,u1_struct_0(A_411),u1_struct_0(B_412))
      | ~ v1_funct_1(C_413)
      | ~ l1_pre_topc(B_412)
      | ~ l1_pre_topc(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2702,plain,
    ( k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2695])).

tff(c_2706,plain,(
    k1_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_52,c_2545,c_2702])).

tff(c_2708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2546,c_2706])).

tff(c_2710,plain,(
    k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') != k2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2717,plain,(
    k2_struct_0('#skF_4') != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2716,c_2710])).

tff(c_2709,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2858,plain,(
    ! [A_457,B_458,C_459] :
      ( k2_relset_1(u1_struct_0(A_457),u1_struct_0(B_458),C_459) = k2_struct_0(B_458)
      | ~ v3_tops_2(C_459,A_457,B_458)
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_457),u1_struct_0(B_458))))
      | ~ v1_funct_2(C_459,u1_struct_0(A_457),u1_struct_0(B_458))
      | ~ v1_funct_1(C_459)
      | ~ l1_pre_topc(B_458)
      | ~ l1_pre_topc(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2865,plain,
    ( k2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5') = k2_struct_0('#skF_4')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2858])).

tff(c_2869,plain,(
    k2_struct_0('#skF_4') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_52,c_2709,c_2716,c_2865])).

tff(c_2871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2717,c_2869])).

tff(c_2873,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2872,plain,(
    v3_tops_2('#skF_5','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2966,plain,(
    ! [C_489,A_490,B_491] :
      ( v2_funct_1(C_489)
      | ~ v3_tops_2(C_489,A_490,B_491)
      | ~ m1_subset_1(C_489,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490),u1_struct_0(B_491))))
      | ~ v1_funct_2(C_489,u1_struct_0(A_490),u1_struct_0(B_491))
      | ~ v1_funct_1(C_489)
      | ~ l1_pre_topc(B_491)
      | ~ l1_pre_topc(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2973,plain,
    ( v2_funct_1('#skF_5')
    | ~ v3_tops_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2966])).

tff(c_2977,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_52,c_2872,c_2973])).

tff(c_2979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2873,c_2977])).

%------------------------------------------------------------------------------
