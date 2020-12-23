%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1804+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 891 expanded)
%              Number of leaves         :   36 ( 298 expanded)
%              Depth                    :   14
%              Number of atoms          :  477 (4582 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k9_tmap_1 > k8_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_228,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_tsep_1(B,C)
                 => ( v1_funct_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C))
                    & v1_funct_2(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C),u1_struct_0(C),u1_struct_0(k8_tmap_1(A,B)))
                    & v5_pre_topc(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C),C,k8_tmap_1(A,B))
                    & m1_subset_1(k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(k8_tmap_1(A,B))))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_tmap_1)).

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

tff(f_198,axiom,(
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

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tsep_1(B,C)
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(C))
                   => r1_tmap_1(C,k8_tmap_1(A,B),k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_tmap_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

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

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_241,plain,(
    ! [B_160,A_161] :
      ( l1_pre_topc(B_160)
      | ~ m1_pre_topc(B_160,A_161)
      | ~ l1_pre_topc(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_247,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_241])).

tff(c_253,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_247])).

tff(c_22,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k9_tmap_1(A_29,B_30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_29),u1_struct_0(k8_tmap_1(A_29,B_30)))))
      | ~ m1_pre_topc(B_30,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_457,plain,(
    ! [A_249,B_250,C_251,D_252] :
      ( v1_funct_2(k2_tmap_1(A_249,B_250,C_251,D_252),u1_struct_0(D_252),u1_struct_0(B_250))
      | ~ l1_struct_0(D_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_249),u1_struct_0(B_250))))
      | ~ v1_funct_2(C_251,u1_struct_0(A_249),u1_struct_0(B_250))
      | ~ v1_funct_1(C_251)
      | ~ l1_struct_0(B_250)
      | ~ l1_struct_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_547,plain,(
    ! [A_296,B_297,D_298] :
      ( v1_funct_2(k2_tmap_1(A_296,k8_tmap_1(A_296,B_297),k9_tmap_1(A_296,B_297),D_298),u1_struct_0(D_298),u1_struct_0(k8_tmap_1(A_296,B_297)))
      | ~ l1_struct_0(D_298)
      | ~ v1_funct_2(k9_tmap_1(A_296,B_297),u1_struct_0(A_296),u1_struct_0(k8_tmap_1(A_296,B_297)))
      | ~ v1_funct_1(k9_tmap_1(A_296,B_297))
      | ~ l1_struct_0(k8_tmap_1(A_296,B_297))
      | ~ l1_struct_0(A_296)
      | ~ m1_pre_topc(B_297,A_296)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(resolution,[status(thm)],[c_22,c_457])).

tff(c_307,plain,(
    ! [A_202,B_203,C_204,D_205] :
      ( m1_subset_1(k2_tmap_1(A_202,B_203,C_204,D_205),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_205),u1_struct_0(B_203))))
      | ~ l1_struct_0(D_205)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_202),u1_struct_0(B_203))))
      | ~ v1_funct_2(C_204,u1_struct_0(A_202),u1_struct_0(B_203))
      | ~ v1_funct_1(C_204)
      | ~ l1_struct_0(B_203)
      | ~ l1_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_65,plain,(
    ! [B_79,A_80] :
      ( l1_pre_topc(B_79)
      | ~ m1_pre_topc(B_79,A_80)
      | ~ l1_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_71,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_65])).

tff(c_77,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_71])).

tff(c_114,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( v1_funct_1(k2_tmap_1(A_113,B_114,C_115,D_116))
      | ~ l1_struct_0(D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_113),u1_struct_0(B_114))))
      | ~ v1_funct_2(C_115,u1_struct_0(A_113),u1_struct_0(B_114))
      | ~ v1_funct_1(C_115)
      | ~ l1_struct_0(B_114)
      | ~ l1_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_173,plain,(
    ! [A_150,B_151,D_152] :
      ( v1_funct_1(k2_tmap_1(A_150,k8_tmap_1(A_150,B_151),k9_tmap_1(A_150,B_151),D_152))
      | ~ l1_struct_0(D_152)
      | ~ v1_funct_2(k9_tmap_1(A_150,B_151),u1_struct_0(A_150),u1_struct_0(k8_tmap_1(A_150,B_151)))
      | ~ v1_funct_1(k9_tmap_1(A_150,B_151))
      | ~ l1_struct_0(k8_tmap_1(A_150,B_151))
      | ~ l1_struct_0(A_150)
      | ~ m1_pre_topc(B_151,A_150)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_22,c_114])).

tff(c_177,plain,(
    ! [A_153,B_154,D_155] :
      ( v1_funct_1(k2_tmap_1(A_153,k8_tmap_1(A_153,B_154),k9_tmap_1(A_153,B_154),D_155))
      | ~ l1_struct_0(D_155)
      | ~ v1_funct_1(k9_tmap_1(A_153,B_154))
      | ~ l1_struct_0(k8_tmap_1(A_153,B_154))
      | ~ l1_struct_0(A_153)
      | ~ m1_pre_topc(B_154,A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_24,c_173])).

tff(c_46,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_64,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_180,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_177,c_64])).

tff(c_183,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_180])).

tff(c_184,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_183])).

tff(c_185,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_188,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_188])).

tff(c_193,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_195,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_198,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_198])).

tff(c_203,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_216,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_220,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_216])).

tff(c_223,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_220])).

tff(c_226,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_223])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_226])).

tff(c_229,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_233,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_229])).

tff(c_236,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_233])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_236])).

tff(c_239,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_268,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_322,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_307,c_268])).

tff(c_324,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_328,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_324])).

tff(c_332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_328])).

tff(c_333,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_335,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_338,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_335])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_338])).

tff(c_343,plain,
    ( ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_345,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_349,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_345])).

tff(c_352,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_349])).

tff(c_355,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_352])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_355])).

tff(c_358,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_361,plain,(
    ~ m1_subset_1(k9_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_364,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_361])).

tff(c_367,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_364])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_367])).

tff(c_370,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_388,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_391,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_388])).

tff(c_394,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_391])).

tff(c_396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_394])).

tff(c_397,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_401,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_397])).

tff(c_404,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_401])).

tff(c_406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_404])).

tff(c_407,plain,
    ( ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_419,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_550,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_547,c_419])).

tff(c_553,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_550])).

tff(c_554,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_553])).

tff(c_555,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_554])).

tff(c_558,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_555])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_558])).

tff(c_563,plain,
    ( ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_554])).

tff(c_566,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_563])).

tff(c_569,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_566])).

tff(c_573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_569])).

tff(c_574,plain,
    ( ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_563])).

tff(c_576,plain,(
    ~ l1_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_580,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_576])).

tff(c_583,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_580])).

tff(c_586,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_583])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_586])).

tff(c_589,plain,
    ( ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_591,plain,(
    ~ v1_funct_2(k9_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_589])).

tff(c_594,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_591])).

tff(c_597,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_594])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_597])).

tff(c_600,plain,(
    ~ v1_funct_1(k9_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_589])).

tff(c_608,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_600])).

tff(c_611,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_608])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_611])).

tff(c_614,plain,(
    ~ v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_254,plain,(
    ! [B_162,A_163] :
      ( v2_pre_topc(B_162)
      | ~ m1_pre_topc(B_162,A_163)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_260,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_254])).

tff(c_266,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_260])).

tff(c_240,plain,(
    v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_615,plain,(
    v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_408,plain,(
    m1_subset_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3'))))) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_707,plain,(
    ! [A_346,B_347,C_348] :
      ( m1_subset_1('#skF_1'(A_346,B_347,C_348),u1_struct_0(B_347))
      | v5_pre_topc(C_348,B_347,A_346)
      | ~ m1_subset_1(C_348,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_347),u1_struct_0(A_346))))
      | ~ v1_funct_2(C_348,u1_struct_0(B_347),u1_struct_0(A_346))
      | ~ v1_funct_1(C_348)
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_716,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_408,c_707])).

tff(c_722,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_253,c_240,c_615,c_716])).

tff(c_723,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_614,c_722])).

tff(c_724,plain,(
    ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_727,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_724])).

tff(c_730,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_727])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_730])).

tff(c_733,plain,
    ( ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_735,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_733])).

tff(c_738,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_735])).

tff(c_741,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_738])).

tff(c_743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_741])).

tff(c_744,plain,
    ( m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_733])).

tff(c_751,plain,(
    v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_744])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( ~ v2_struct_0(k8_tmap_1(A_35,B_36))
      | ~ m1_pre_topc(B_36,A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_754,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_751,c_36])).

tff(c_757,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_754])).

tff(c_759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_757])).

tff(c_761,plain,(
    ~ v2_struct_0(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_744])).

tff(c_48,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_760,plain,(
    m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_744])).

tff(c_734,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_745,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_733])).

tff(c_38,plain,(
    ! [C_49,A_37,B_45,D_51] :
      ( r1_tmap_1(C_49,k8_tmap_1(A_37,B_45),k2_tmap_1(A_37,k8_tmap_1(A_37,B_45),k9_tmap_1(A_37,B_45),C_49),D_51)
      | ~ m1_subset_1(D_51,u1_struct_0(C_49))
      | ~ r1_tsep_1(B_45,C_49)
      | ~ m1_pre_topc(C_49,A_37)
      | v2_struct_0(C_49)
      | ~ m1_pre_topc(B_45,A_37)
      | v2_struct_0(B_45)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_746,plain,(
    ! [B_349,A_350,C_351] :
      ( ~ r1_tmap_1(B_349,A_350,C_351,'#skF_1'(A_350,B_349,C_351))
      | v5_pre_topc(C_351,B_349,A_350)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_349),u1_struct_0(A_350))))
      | ~ v1_funct_2(C_351,u1_struct_0(B_349),u1_struct_0(A_350))
      | ~ v1_funct_1(C_351)
      | ~ l1_pre_topc(B_349)
      | ~ v2_pre_topc(B_349)
      | v2_struct_0(B_349)
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350)
      | v2_struct_0(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_1406,plain,(
    ! [A_531,B_532,C_533] :
      ( v5_pre_topc(k2_tmap_1(A_531,k8_tmap_1(A_531,B_532),k9_tmap_1(A_531,B_532),C_533),C_533,k8_tmap_1(A_531,B_532))
      | ~ m1_subset_1(k2_tmap_1(A_531,k8_tmap_1(A_531,B_532),k9_tmap_1(A_531,B_532),C_533),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_533),u1_struct_0(k8_tmap_1(A_531,B_532)))))
      | ~ v1_funct_2(k2_tmap_1(A_531,k8_tmap_1(A_531,B_532),k9_tmap_1(A_531,B_532),C_533),u1_struct_0(C_533),u1_struct_0(k8_tmap_1(A_531,B_532)))
      | ~ v1_funct_1(k2_tmap_1(A_531,k8_tmap_1(A_531,B_532),k9_tmap_1(A_531,B_532),C_533))
      | ~ l1_pre_topc(C_533)
      | ~ v2_pre_topc(C_533)
      | ~ l1_pre_topc(k8_tmap_1(A_531,B_532))
      | ~ v2_pre_topc(k8_tmap_1(A_531,B_532))
      | v2_struct_0(k8_tmap_1(A_531,B_532))
      | ~ m1_subset_1('#skF_1'(k8_tmap_1(A_531,B_532),C_533,k2_tmap_1(A_531,k8_tmap_1(A_531,B_532),k9_tmap_1(A_531,B_532),C_533)),u1_struct_0(C_533))
      | ~ r1_tsep_1(B_532,C_533)
      | ~ m1_pre_topc(C_533,A_531)
      | v2_struct_0(C_533)
      | ~ m1_pre_topc(B_532,A_531)
      | v2_struct_0(B_532)
      | ~ l1_pre_topc(A_531)
      | ~ v2_pre_topc(A_531)
      | v2_struct_0(A_531) ) ),
    inference(resolution,[status(thm)],[c_38,c_746])).

tff(c_1414,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_4'),u1_struct_0(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'(k8_tmap_1('#skF_2','#skF_3'),'#skF_4',k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4')),u1_struct_0('#skF_4'))
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_408,c_1406])).

tff(c_1419,plain,
    ( v5_pre_topc(k2_tmap_1('#skF_2',k8_tmap_1('#skF_2','#skF_3'),k9_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_50,c_48,c_760,c_734,c_745,c_266,c_253,c_240,c_615,c_1414])).

tff(c_1421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_52,c_761,c_614,c_1419])).

%------------------------------------------------------------------------------
