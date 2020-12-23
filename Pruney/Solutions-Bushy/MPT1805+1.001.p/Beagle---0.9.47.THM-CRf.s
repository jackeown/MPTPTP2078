%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1805+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:26 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 884 expanded)
%              Number of leaves         :   35 ( 294 expanded)
%              Depth                    :   14
%              Number of atoms          :  452 (3954 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k9_tmap_1,type,(
    k9_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_193,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( v1_funct_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B))
              & v1_funct_2(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),u1_struct_0(B),u1_struct_0(k8_tmap_1(A,B)))
              & v5_pre_topc(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),B,k8_tmap_1(A,B))
              & m1_subset_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(k8_tmap_1(A,B))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_tmap_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( ~ v2_struct_0(k8_tmap_1(A,B))
        & v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_171,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

tff(f_142,axiom,(
    ! [A] :
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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( l1_pre_topc(k8_tmap_1(A_11,B_12))
      | ~ m1_pre_topc(B_12,A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( v2_pre_topc(k8_tmap_1(A_20,B_21))
      | ~ m1_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( v1_funct_1(k9_tmap_1(A_13,B_14))
      | ~ m1_pre_topc(B_14,A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( v1_funct_2(k9_tmap_1(A_13,B_14),u1_struct_0(A_13),u1_struct_0(k8_tmap_1(A_13,B_14)))
      | ~ m1_pre_topc(B_14,A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    ! [B_53,A_54] :
      ( l1_pre_topc(B_53)
      | ~ m1_pre_topc(B_53,A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_60])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_63])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k9_tmap_1(A_13,B_14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13),u1_struct_0(k8_tmap_1(A_13,B_14)))))
      | ~ m1_pre_topc(B_14,A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_371,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( v1_funct_2(k2_tmap_1(A_172,B_173,C_174,D_175),u1_struct_0(D_175),u1_struct_0(B_173))
      | ~ l1_struct_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_172),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_struct_0(B_173)
      | ~ l1_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_411,plain,(
    ! [A_196,B_197,D_198] :
      ( v1_funct_2(k2_tmap_1(A_196,k8_tmap_1(A_196,B_197),k9_tmap_1(A_196,B_197),D_198),u1_struct_0(D_198),u1_struct_0(k8_tmap_1(A_196,B_197)))
      | ~ l1_struct_0(D_198)
      | ~ v1_funct_2(k9_tmap_1(A_196,B_197),u1_struct_0(A_196),u1_struct_0(k8_tmap_1(A_196,B_197)))
      | ~ v1_funct_1(k9_tmap_1(A_196,B_197))
      | ~ l1_struct_0(k8_tmap_1(A_196,B_197))
      | ~ l1_struct_0(A_196)
      | ~ m1_pre_topc(B_197,A_196)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_22,c_371])).

tff(c_249,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( m1_subset_1(k2_tmap_1(A_149,B_150,C_151,D_152),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_152),u1_struct_0(B_150))))
      | ~ l1_struct_0(D_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_149),u1_struct_0(B_150))))
      | ~ v1_funct_2(C_151,u1_struct_0(A_149),u1_struct_0(B_150))
      | ~ v1_funct_1(C_151)
      | ~ l1_struct_0(B_150)
      | ~ l1_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_110,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( v1_funct_1(k2_tmap_1(A_79,B_80,C_81,D_82))
      | ~ l1_struct_0(D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_79),u1_struct_0(B_80))))
      | ~ v1_funct_2(C_81,u1_struct_0(A_79),u1_struct_0(B_80))
      | ~ v1_funct_1(C_81)
      | ~ l1_struct_0(B_80)
      | ~ l1_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_139,plain,(
    ! [A_104,B_105,D_106] :
      ( v1_funct_1(k2_tmap_1(A_104,k8_tmap_1(A_104,B_105),k9_tmap_1(A_104,B_105),D_106))
      | ~ l1_struct_0(D_106)
      | ~ v1_funct_2(k9_tmap_1(A_104,B_105),u1_struct_0(A_104),u1_struct_0(k8_tmap_1(A_104,B_105)))
      | ~ v1_funct_1(k9_tmap_1(A_104,B_105))
      | ~ l1_struct_0(k8_tmap_1(A_104,B_105))
      | ~ l1_struct_0(A_104)
      | ~ m1_pre_topc(B_105,A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_22,c_110])).

tff(c_143,plain,(
    ! [A_107,B_108,D_109] :
      ( v1_funct_1(k2_tmap_1(A_107,k8_tmap_1(A_107,B_108),k9_tmap_1(A_107,B_108),D_109))
      | ~ l1_struct_0(D_109)
      | ~ v1_funct_1(k9_tmap_1(A_107,B_108))
      | ~ l1_struct_0(k8_tmap_1(A_107,B_108))
      | ~ l1_struct_0(A_107)
      | ~ m1_pre_topc(B_108,A_107)
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_24,c_139])).

tff(c_48,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_68,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_146,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_143,c_68])).

tff(c_149,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_146])).

tff(c_150,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_149])).

tff(c_151,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_155,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_155])).

tff(c_160,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_162,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_165,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_162])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_165])).

tff(c_170,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_172,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_176,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_172])).

tff(c_179,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_182,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_179])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_182])).

tff(c_185,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_190,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_185])).

tff(c_193,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_190])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_193])).

tff(c_196,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_236,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_259,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_249,c_236])).

tff(c_260,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_263,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_263])).

tff(c_268,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_270,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_273,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_270])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_273])).

tff(c_278,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_280,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_291,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_280])).

tff(c_294,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_291])).

tff(c_297,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_294])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_297])).

tff(c_300,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_302,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_305,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_302])).

tff(c_308,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_305])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_308])).

tff(c_311,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_323,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_326,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_323])).

tff(c_329,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_326])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_329])).

tff(c_332,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_349,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_332])).

tff(c_352,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_349])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_352])).

tff(c_355,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_358,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_414,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_411,c_358])).

tff(c_417,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_414])).

tff(c_418,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_417])).

tff(c_419,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_422,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_419])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_422])).

tff(c_427,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_433,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_427])).

tff(c_436,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_433])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_436])).

tff(c_441,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_427])).

tff(c_443,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_447,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_443])).

tff(c_450,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_447])).

tff(c_453,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_450])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_453])).

tff(c_456,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_458,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_465,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_458])).

tff(c_468,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_465])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_468])).

tff(c_471,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_475,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_471])).

tff(c_478,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_475])).

tff(c_480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_478])).

tff(c_481,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_204,plain,(
    ! [B_118,A_119] :
      ( v2_pre_topc(B_118)
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_207,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_204])).

tff(c_210,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_207])).

tff(c_197,plain,(
    v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_482,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_356,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_538,plain,(
    ! [A_230,B_231,C_232] :
      ( m1_subset_1('#skF_1'(A_230,B_231,C_232),u1_struct_0(B_231))
      | v5_pre_topc(C_232,B_231,A_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_231),u1_struct_0(A_230))))
      | ~ v1_funct_2(C_232,u1_struct_0(B_231),u1_struct_0(A_230))
      | ~ v1_funct_1(C_232)
      | ~ l1_pre_topc(B_231)
      | ~ v2_pre_topc(B_231)
      | v2_struct_0(B_231)
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_544,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_356,c_538])).

tff(c_549,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_66,c_197,c_482,c_544])).

tff(c_550,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_481,c_549])).

tff(c_551,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_554,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_551])).

tff(c_557,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_554])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_557])).

tff(c_560,plain,
    ( ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_562,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_565,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_562])).

tff(c_568,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_565])).

tff(c_570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_568])).

tff(c_571,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_573,plain,(
    v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_571])).

tff(c_38,plain,(
    ! [A_20,B_21] :
      ( ~ v2_struct_0(k8_tmap_1(A_20,B_21))
      | ~ m1_pre_topc(B_21,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_576,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_573,c_38])).

tff(c_579,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_576])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_579])).

tff(c_583,plain,(
    ~ v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_582,plain,(
    m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_571])).

tff(c_561,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_572,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_40,plain,(
    ! [B_26,A_22,C_28] :
      ( r1_tmap_1(B_26,k8_tmap_1(A_22,B_26),k2_tmap_1(A_22,k8_tmap_1(A_22,B_26),k9_tmap_1(A_22,B_26),B_26),C_28)
      | ~ m1_subset_1(C_28,u1_struct_0(B_26))
      | ~ m1_pre_topc(B_26,A_22)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_584,plain,(
    ! [B_233,A_234,C_235] :
      ( ~ r1_tmap_1(B_233,A_234,C_235,'#skF_1'(A_234,B_233,C_235))
      | v5_pre_topc(C_235,B_233,A_234)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_233),u1_struct_0(A_234))))
      | ~ v1_funct_2(C_235,u1_struct_0(B_233),u1_struct_0(A_234))
      | ~ v1_funct_1(C_235)
      | ~ l1_pre_topc(B_233)
      | ~ v2_pre_topc(B_233)
      | v2_struct_0(B_233)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_712,plain,(
    ! [A_299,B_300] :
      ( v5_pre_topc(k2_tmap_1(A_299,k8_tmap_1(A_299,B_300),k9_tmap_1(A_299,B_300),B_300),B_300,k8_tmap_1(A_299,B_300))
      | ~ m1_subset_1(k2_tmap_1(A_299,k8_tmap_1(A_299,B_300),k9_tmap_1(A_299,B_300),B_300),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_300),u1_struct_0(k8_tmap_1(A_299,B_300)))))
      | ~ v1_funct_2(k2_tmap_1(A_299,k8_tmap_1(A_299,B_300),k9_tmap_1(A_299,B_300),B_300),u1_struct_0(B_300),u1_struct_0(k8_tmap_1(A_299,B_300)))
      | ~ v1_funct_1(k2_tmap_1(A_299,k8_tmap_1(A_299,B_300),k9_tmap_1(A_299,B_300),B_300))
      | ~ l1_pre_topc(B_300)
      | ~ v2_pre_topc(B_300)
      | ~ l1_pre_topc(k8_tmap_1(A_299,B_300))
      | ~ v2_pre_topc(k8_tmap_1(A_299,B_300))
      | v2_struct_0(k8_tmap_1(A_299,B_300))
      | ~ m1_subset_1('#skF_1'(k8_tmap_1(A_299,B_300),B_300,k2_tmap_1(A_299,k8_tmap_1(A_299,B_300),k9_tmap_1(A_299,B_300),B_300)),u1_struct_0(B_300))
      | ~ m1_pre_topc(B_300,A_299)
      | v2_struct_0(B_300)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(resolution,[status(thm)],[c_40,c_584])).

tff(c_717,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_356,c_712])).

tff(c_721,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_50,c_582,c_561,c_572,c_210,c_66,c_197,c_482,c_717])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_583,c_481,c_721])).

%------------------------------------------------------------------------------
