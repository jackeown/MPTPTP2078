%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1805+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:27 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 883 expanded)
%              Number of leaves         :   34 ( 293 expanded)
%              Depth                    :   14
%              Number of atoms          :  452 (3954 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k9_tmap_1 > k8_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_212,negated_conjecture,(
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

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( ~ v2_struct_0(k8_tmap_1(A,B))
        & v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_86,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_190,axiom,(
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

tff(f_161,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_16,plain,(
    ! [A_27,B_28] :
      ( l1_pre_topc(k8_tmap_1(A_27,B_28))
      | ~ m1_pre_topc(B_28,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    ! [A_35,B_36] :
      ( v2_pre_topc(k8_tmap_1(A_35,B_36))
      | ~ m1_pre_topc(B_36,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( v1_funct_1(k9_tmap_1(A_29,B_30))
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( v1_funct_2(k9_tmap_1(A_29,B_30),u1_struct_0(A_29),u1_struct_0(k8_tmap_1(A_29,B_30)))
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_28,plain,(
    ! [A_31] :
      ( l1_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_58,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_61,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_58])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_61])).

tff(c_22,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k9_tmap_1(A_29,B_30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_29),u1_struct_0(k8_tmap_1(A_29,B_30)))))
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_442,plain,(
    ! [A_240,B_241,C_242,D_243] :
      ( v1_funct_2(k2_tmap_1(A_240,B_241,C_242,D_243),u1_struct_0(D_243),u1_struct_0(B_241))
      | ~ l1_struct_0(D_243)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_240),u1_struct_0(B_241))))
      | ~ v1_funct_2(C_242,u1_struct_0(A_240),u1_struct_0(B_241))
      | ~ v1_funct_1(C_242)
      | ~ l1_struct_0(B_241)
      | ~ l1_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_531,plain,(
    ! [A_283,B_284,D_285] :
      ( v1_funct_2(k2_tmap_1(A_283,k8_tmap_1(A_283,B_284),k9_tmap_1(A_283,B_284),D_285),u1_struct_0(D_285),u1_struct_0(k8_tmap_1(A_283,B_284)))
      | ~ l1_struct_0(D_285)
      | ~ v1_funct_2(k9_tmap_1(A_283,B_284),u1_struct_0(A_283),u1_struct_0(k8_tmap_1(A_283,B_284)))
      | ~ v1_funct_1(k9_tmap_1(A_283,B_284))
      | ~ l1_struct_0(k8_tmap_1(A_283,B_284))
      | ~ l1_struct_0(A_283)
      | ~ m1_pre_topc(B_284,A_283)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(resolution,[status(thm)],[c_22,c_442])).

tff(c_275,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( m1_subset_1(k2_tmap_1(A_193,B_194,C_195,D_196),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_196),u1_struct_0(B_194))))
      | ~ l1_struct_0(D_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),u1_struct_0(B_194))))
      | ~ v1_funct_2(C_195,u1_struct_0(A_193),u1_struct_0(B_194))
      | ~ v1_funct_1(C_195)
      | ~ l1_struct_0(B_194)
      | ~ l1_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_96,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( v1_funct_1(k2_tmap_1(A_102,B_103,C_104,D_105))
      | ~ l1_struct_0(D_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),u1_struct_0(B_103))))
      | ~ v1_funct_2(C_104,u1_struct_0(A_102),u1_struct_0(B_103))
      | ~ v1_funct_1(C_104)
      | ~ l1_struct_0(B_103)
      | ~ l1_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_155,plain,(
    ! [A_138,B_139,D_140] :
      ( v1_funct_1(k2_tmap_1(A_138,k8_tmap_1(A_138,B_139),k9_tmap_1(A_138,B_139),D_140))
      | ~ l1_struct_0(D_140)
      | ~ v1_funct_2(k9_tmap_1(A_138,B_139),u1_struct_0(A_138),u1_struct_0(k8_tmap_1(A_138,B_139)))
      | ~ v1_funct_1(k9_tmap_1(A_138,B_139))
      | ~ l1_struct_0(k8_tmap_1(A_138,B_139))
      | ~ l1_struct_0(A_138)
      | ~ m1_pre_topc(B_139,A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_159,plain,(
    ! [A_141,B_142,D_143] :
      ( v1_funct_1(k2_tmap_1(A_141,k8_tmap_1(A_141,B_142),k9_tmap_1(A_141,B_142),D_143))
      | ~ l1_struct_0(D_143)
      | ~ v1_funct_1(k9_tmap_1(A_141,B_142))
      | ~ l1_struct_0(k8_tmap_1(A_141,B_142))
      | ~ l1_struct_0(A_141)
      | ~ m1_pre_topc(B_142,A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_24,c_155])).

tff(c_46,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_72,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_162,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_159,c_72])).

tff(c_165,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_162])).

tff(c_166,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_165])).

tff(c_167,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_181,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_167])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_181])).

tff(c_186,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_188,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_191,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_191])).

tff(c_196,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_198,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_202,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_198])).

tff(c_205,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_202])).

tff(c_208,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_205])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_208])).

tff(c_211,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_226,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_211])).

tff(c_229,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_226])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_229])).

tff(c_232,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_234,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_290,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_275,c_234])).

tff(c_292,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_295,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_292])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_295])).

tff(c_300,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_302,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_305,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_302])).

tff(c_309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_305])).

tff(c_310,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_312,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_316,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_312])).

tff(c_319,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_316])).

tff(c_322,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_319])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_322])).

tff(c_325,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_338,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_341,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_338])).

tff(c_344,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_341])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_344])).

tff(c_347,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_371,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_374,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_371])).

tff(c_377,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_374])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_377])).

tff(c_380,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_384,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_380])).

tff(c_387,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_384])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_387])).

tff(c_390,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_440,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_534,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_531,c_440])).

tff(c_537,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_534])).

tff(c_538,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_537])).

tff(c_540,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_543,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_540])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_543])).

tff(c_548,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_550,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_553,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_550])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_553])).

tff(c_558,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_560,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_564,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_560])).

tff(c_567,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_564])).

tff(c_570,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_567])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_570])).

tff(c_573,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_579,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_582,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_579])).

tff(c_585,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_582])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_585])).

tff(c_588,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_592,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_588])).

tff(c_595,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_592])).

tff(c_597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_595])).

tff(c_598,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_65,plain,(
    ! [B_70,A_71] :
      ( v2_pre_topc(B_70)
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_71,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_68])).

tff(c_233,plain,(
    v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_599,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_391,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_670,plain,(
    ! [A_318,B_319,C_320] :
      ( m1_subset_1('#skF_1'(A_318,B_319,C_320),u1_struct_0(B_319))
      | v5_pre_topc(C_320,B_319,A_318)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_319),u1_struct_0(A_318))))
      | ~ v1_funct_2(C_320,u1_struct_0(B_319),u1_struct_0(A_318))
      | ~ v1_funct_1(C_320)
      | ~ l1_pre_topc(B_319)
      | ~ v2_pre_topc(B_319)
      | v2_struct_0(B_319)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_679,plain,
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
    inference(resolution,[status(thm)],[c_391,c_670])).

tff(c_685,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_64,c_233,c_599,c_679])).

tff(c_686,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_598,c_685])).

tff(c_687,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_686])).

tff(c_690,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_687])).

tff(c_693,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_690])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_693])).

tff(c_696,plain,
    ( ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_686])).

tff(c_698,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_696])).

tff(c_701,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_698])).

tff(c_704,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_701])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_704])).

tff(c_707,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_696])).

tff(c_709,plain,(
    v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( ~ v2_struct_0(k8_tmap_1(A_35,B_36))
      | ~ m1_pre_topc(B_36,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_717,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_709,c_36])).

tff(c_720,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_717])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_720])).

tff(c_724,plain,(
    ~ v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_723,plain,(
    m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_3',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_697,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_686])).

tff(c_708,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_696])).

tff(c_38,plain,(
    ! [B_41,A_37,C_43] :
      ( r1_tmap_1(B_41,k8_tmap_1(A_37,B_41),k2_tmap_1(A_37,k8_tmap_1(A_37,B_41),k9_tmap_1(A_37,B_41),B_41),C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(B_41))
      | ~ m1_pre_topc(B_41,A_37)
      | v2_struct_0(B_41)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_728,plain,(
    ! [B_325,A_326,C_327] :
      ( ~ r1_tmap_1(B_325,A_326,C_327,'#skF_1'(A_326,B_325,C_327))
      | v5_pre_topc(C_327,B_325,A_326)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_325),u1_struct_0(A_326))))
      | ~ v1_funct_2(C_327,u1_struct_0(B_325),u1_struct_0(A_326))
      | ~ v1_funct_1(C_327)
      | ~ l1_pre_topc(B_325)
      | ~ v2_pre_topc(B_325)
      | v2_struct_0(B_325)
      | ~ l1_pre_topc(A_326)
      | ~ v2_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1391,plain,(
    ! [A_510,B_511] :
      ( v5_pre_topc(k2_tmap_1(A_510,k8_tmap_1(A_510,B_511),k9_tmap_1(A_510,B_511),B_511),B_511,k8_tmap_1(A_510,B_511))
      | ~ m1_subset_1(k2_tmap_1(A_510,k8_tmap_1(A_510,B_511),k9_tmap_1(A_510,B_511),B_511),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_511),u1_struct_0(k8_tmap_1(A_510,B_511)))))
      | ~ v1_funct_2(k2_tmap_1(A_510,k8_tmap_1(A_510,B_511),k9_tmap_1(A_510,B_511),B_511),u1_struct_0(B_511),u1_struct_0(k8_tmap_1(A_510,B_511)))
      | ~ v1_funct_1(k2_tmap_1(A_510,k8_tmap_1(A_510,B_511),k9_tmap_1(A_510,B_511),B_511))
      | ~ l1_pre_topc(B_511)
      | ~ v2_pre_topc(B_511)
      | ~ l1_pre_topc(k8_tmap_1(A_510,B_511))
      | ~ v2_pre_topc(k8_tmap_1(A_510,B_511))
      | v2_struct_0(k8_tmap_1(A_510,B_511))
      | ~ m1_subset_1('#skF_1'(k8_tmap_1(A_510,B_511),B_511,k2_tmap_1(A_510,k8_tmap_1(A_510,B_511),k9_tmap_1(A_510,B_511),B_511)),u1_struct_0(B_511))
      | ~ m1_pre_topc(B_511,A_510)
      | v2_struct_0(B_511)
      | ~ l1_pre_topc(A_510)
      | ~ v2_pre_topc(A_510)
      | v2_struct_0(A_510) ) ),
    inference(resolution,[status(thm)],[c_38,c_728])).

tff(c_1399,plain,
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
    inference(resolution,[status(thm)],[c_391,c_1391])).

tff(c_1404,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_3'),'#skF_3',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_723,c_697,c_708,c_71,c_64,c_233,c_599,c_1399])).

tff(c_1406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_724,c_598,c_1404])).

%------------------------------------------------------------------------------
