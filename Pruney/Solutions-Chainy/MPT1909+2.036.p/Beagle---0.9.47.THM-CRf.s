%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:42 EST 2020

% Result     : Theorem 23.10s
% Output     : CNFRefutation 23.30s
% Verified   : 
% Statistics : Number of formulae       :  257 (2132 expanded)
%              Number of leaves         :   58 ( 728 expanded)
%              Depth                    :   33
%              Number of atoms          : 1046 (11172 expanded)
%              Number of equality atoms :  181 (1959 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_borsuk_1,type,(
    v3_borsuk_1: ( $i * $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_224,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & v5_pre_topc(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( v3_borsuk_1(C,A,B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( D = E
                           => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k6_domain_1(u1_struct_0(B),D)) = k2_pre_topc(A,k6_domain_1(u1_struct_0(A),E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tex_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ! [C] :
          ( m1_subset_1(C,A)
         => ! [D] :
              ( m1_subset_1(D,A)
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ! [F] :
                      ( m1_subset_1(F,A)
                     => ! [G] :
                          ( m1_subset_1(G,A)
                         => ! [H] :
                              ( m1_subset_1(H,A)
                             => ! [I] :
                                  ( m1_subset_1(I,A)
                                 => ( A != k1_xboole_0
                                   => m1_subset_1(k6_enumset1(B,C,D,E,F,G,H,I),k1_zfmisc_1(A)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_30,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_32,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_91,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_185,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_tex_2(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & v5_pre_topc(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v3_borsuk_1(C,A,B)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                       => ( D = E
                         => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D) = k2_pre_topc(A,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tex_2)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_812,plain,(
    ! [F_676,I_675,C_670,H_673,D_669,E_674,G_668,A_672,B_671] :
      ( m1_subset_1(k6_enumset1(B_671,C_670,D_669,E_674,F_676,G_668,H_673,I_675),k1_zfmisc_1(A_672))
      | k1_xboole_0 = A_672
      | ~ m1_subset_1(I_675,A_672)
      | ~ m1_subset_1(H_673,A_672)
      | ~ m1_subset_1(G_668,A_672)
      | ~ m1_subset_1(F_676,A_672)
      | ~ m1_subset_1(E_674,A_672)
      | ~ m1_subset_1(D_669,A_672)
      | ~ m1_subset_1(C_670,A_672)
      | ~ m1_subset_1(B_671,A_672) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    ! [C_312,A_306,B_310] :
      ( m1_subset_1(C_312,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ m1_subset_1(C_312,k1_zfmisc_1(u1_struct_0(B_310)))
      | ~ m1_pre_topc(B_310,A_306)
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18185,plain,(
    ! [A_2285,B_2288,B_2287,G_2280,F_2281,D_2279,E_2283,I_2282,H_2286,C_2284] :
      ( m1_subset_1(k6_enumset1(B_2287,C_2284,D_2279,E_2283,F_2281,G_2280,H_2286,I_2282),k1_zfmisc_1(u1_struct_0(A_2285)))
      | ~ m1_pre_topc(B_2288,A_2285)
      | ~ l1_pre_topc(A_2285)
      | u1_struct_0(B_2288) = k1_xboole_0
      | ~ m1_subset_1(I_2282,u1_struct_0(B_2288))
      | ~ m1_subset_1(H_2286,u1_struct_0(B_2288))
      | ~ m1_subset_1(G_2280,u1_struct_0(B_2288))
      | ~ m1_subset_1(F_2281,u1_struct_0(B_2288))
      | ~ m1_subset_1(E_2283,u1_struct_0(B_2288))
      | ~ m1_subset_1(D_2279,u1_struct_0(B_2288))
      | ~ m1_subset_1(C_2284,u1_struct_0(B_2288))
      | ~ m1_subset_1(B_2287,u1_struct_0(B_2288)) ) ),
    inference(resolution,[status(thm)],[c_812,c_28])).

tff(c_18187,plain,(
    ! [B_2287,G_2280,F_2281,D_2279,E_2283,I_2282,H_2286,C_2284] :
      ( m1_subset_1(k6_enumset1(B_2287,C_2284,D_2279,E_2283,F_2281,G_2280,H_2286,I_2282),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | u1_struct_0('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(I_2282,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_2286,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_2280,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_2281,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_2283,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_2279,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2284,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_2287,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_64,c_18185])).

tff(c_18190,plain,(
    ! [B_2287,G_2280,F_2281,D_2279,E_2283,I_2282,H_2286,C_2284] :
      ( m1_subset_1(k6_enumset1(B_2287,C_2284,D_2279,E_2283,F_2281,G_2280,H_2286,I_2282),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | u1_struct_0('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(I_2282,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_2286,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_2280,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_2281,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_2283,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_2279,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2284,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_2287,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18187])).

tff(c_18477,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_18190])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_66,plain,(
    v4_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_116,plain,(
    ! [A_398,B_399] :
      ( k6_domain_1(A_398,B_399) = k1_tarski(B_399)
      | ~ m1_subset_1(B_399,A_398)
      | v1_xboole_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_127,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_116])).

tff(c_138,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_32,plain,(
    ! [B_317,A_315] :
      ( m1_subset_1(u1_struct_0(B_317),k1_zfmisc_1(u1_struct_0(A_315)))
      | ~ m1_pre_topc(B_317,A_315)
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_590,plain,(
    ! [B_556,A_557] :
      ( v3_tex_2(u1_struct_0(B_556),A_557)
      | ~ m1_subset_1(u1_struct_0(B_556),k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ v4_tex_2(B_556,A_557)
      | ~ m1_pre_topc(B_556,A_557)
      | ~ l1_pre_topc(A_557)
      | v2_struct_0(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_595,plain,(
    ! [B_558,A_559] :
      ( v3_tex_2(u1_struct_0(B_558),A_559)
      | ~ v4_tex_2(B_558,A_559)
      | v2_struct_0(A_559)
      | ~ m1_pre_topc(B_558,A_559)
      | ~ l1_pre_topc(A_559) ) ),
    inference(resolution,[status(thm)],[c_32,c_590])).

tff(c_534,plain,(
    ! [B_533,A_534] :
      ( ~ v3_tex_2(B_533,A_534)
      | ~ m1_subset_1(B_533,k1_zfmisc_1(u1_struct_0(A_534)))
      | ~ v1_xboole_0(B_533)
      | ~ l1_pre_topc(A_534)
      | ~ v2_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_538,plain,(
    ! [B_317,A_315] :
      ( ~ v3_tex_2(u1_struct_0(B_317),A_315)
      | ~ v1_xboole_0(u1_struct_0(B_317))
      | ~ v2_pre_topc(A_315)
      | v2_struct_0(A_315)
      | ~ m1_pre_topc(B_317,A_315)
      | ~ l1_pre_topc(A_315) ) ),
    inference(resolution,[status(thm)],[c_32,c_534])).

tff(c_600,plain,(
    ! [B_560,A_561] :
      ( ~ v1_xboole_0(u1_struct_0(B_560))
      | ~ v2_pre_topc(A_561)
      | ~ v4_tex_2(B_560,A_561)
      | v2_struct_0(A_561)
      | ~ m1_pre_topc(B_560,A_561)
      | ~ l1_pre_topc(A_561) ) ),
    inference(resolution,[status(thm)],[c_595,c_538])).

tff(c_604,plain,(
    ! [A_562] :
      ( ~ v2_pre_topc(A_562)
      | ~ v4_tex_2('#skF_4',A_562)
      | v2_struct_0(A_562)
      | ~ m1_pre_topc('#skF_4',A_562)
      | ~ l1_pre_topc(A_562) ) ),
    inference(resolution,[status(thm)],[c_138,c_600])).

tff(c_611,plain,
    ( ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_604])).

tff(c_615,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_74,c_611])).

tff(c_617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_615])).

tff(c_619,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_18492,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18477,c_619])).

tff(c_18499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18492])).

tff(c_18501,plain,(
    u1_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_18190])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [G_28,E_26,F_27,A_22,B_23,D_25,C_24] : k6_enumset1(A_22,A_22,B_23,C_24,D_25,E_26,F_27,G_28) = k5_enumset1(A_22,B_23,C_24,D_25,E_26,F_27,G_28) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_871,plain,(
    ! [A_691,A_696,F_694,D_697,C_692,E_693,B_698,G_695] :
      ( m1_subset_1(k5_enumset1(A_691,B_698,C_692,D_697,E_693,F_694,G_695),k1_zfmisc_1(A_696))
      | k1_xboole_0 = A_696
      | ~ m1_subset_1(G_695,A_696)
      | ~ m1_subset_1(F_694,A_696)
      | ~ m1_subset_1(E_693,A_696)
      | ~ m1_subset_1(D_697,A_696)
      | ~ m1_subset_1(C_692,A_696)
      | ~ m1_subset_1(B_698,A_696)
      | ~ m1_subset_1(A_691,A_696)
      | ~ m1_subset_1(A_691,A_696) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_812])).

tff(c_18760,plain,(
    ! [C_2457,B_2453,A_2455,D_2456,F_2451,E_2454,A_2452] :
      ( m1_subset_1(k4_enumset1(A_2455,B_2453,C_2457,D_2456,E_2454,F_2451),k1_zfmisc_1(A_2452))
      | k1_xboole_0 = A_2452
      | ~ m1_subset_1(F_2451,A_2452)
      | ~ m1_subset_1(E_2454,A_2452)
      | ~ m1_subset_1(D_2456,A_2452)
      | ~ m1_subset_1(C_2457,A_2452)
      | ~ m1_subset_1(B_2453,A_2452)
      | ~ m1_subset_1(A_2455,A_2452)
      | ~ m1_subset_1(A_2455,A_2452)
      | ~ m1_subset_1(A_2455,A_2452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_871])).

tff(c_20153,plain,(
    ! [C_2668,A_2669,B_2670,A_2667,D_2671,E_2672] :
      ( m1_subset_1(k3_enumset1(A_2669,B_2670,C_2668,D_2671,E_2672),k1_zfmisc_1(A_2667))
      | k1_xboole_0 = A_2667
      | ~ m1_subset_1(E_2672,A_2667)
      | ~ m1_subset_1(D_2671,A_2667)
      | ~ m1_subset_1(C_2668,A_2667)
      | ~ m1_subset_1(B_2670,A_2667)
      | ~ m1_subset_1(A_2669,A_2667)
      | ~ m1_subset_1(A_2669,A_2667)
      | ~ m1_subset_1(A_2669,A_2667)
      | ~ m1_subset_1(A_2669,A_2667) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_18760])).

tff(c_20377,plain,(
    ! [D_2679,A_2683,B_2680,A_2682,C_2681] :
      ( m1_subset_1(k2_enumset1(A_2682,B_2680,C_2681,D_2679),k1_zfmisc_1(A_2683))
      | k1_xboole_0 = A_2683
      | ~ m1_subset_1(D_2679,A_2683)
      | ~ m1_subset_1(C_2681,A_2683)
      | ~ m1_subset_1(B_2680,A_2683)
      | ~ m1_subset_1(A_2682,A_2683)
      | ~ m1_subset_1(A_2682,A_2683)
      | ~ m1_subset_1(A_2682,A_2683)
      | ~ m1_subset_1(A_2682,A_2683)
      | ~ m1_subset_1(A_2682,A_2683) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_20153])).

tff(c_21125,plain,(
    ! [A_2765,B_2766,C_2767,A_2768] :
      ( m1_subset_1(k1_enumset1(A_2765,B_2766,C_2767),k1_zfmisc_1(A_2768))
      | k1_xboole_0 = A_2768
      | ~ m1_subset_1(C_2767,A_2768)
      | ~ m1_subset_1(B_2766,A_2768)
      | ~ m1_subset_1(A_2765,A_2768)
      | ~ m1_subset_1(A_2765,A_2768)
      | ~ m1_subset_1(A_2765,A_2768)
      | ~ m1_subset_1(A_2765,A_2768)
      | ~ m1_subset_1(A_2765,A_2768)
      | ~ m1_subset_1(A_2765,A_2768) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_20377])).

tff(c_39760,plain,(
    ! [A_4066,B_4067,A_4068] :
      ( m1_subset_1(k2_tarski(A_4066,B_4067),k1_zfmisc_1(A_4068))
      | k1_xboole_0 = A_4068
      | ~ m1_subset_1(B_4067,A_4068)
      | ~ m1_subset_1(A_4066,A_4068)
      | ~ m1_subset_1(A_4066,A_4068)
      | ~ m1_subset_1(A_4066,A_4068)
      | ~ m1_subset_1(A_4066,A_4068)
      | ~ m1_subset_1(A_4066,A_4068)
      | ~ m1_subset_1(A_4066,A_4068)
      | ~ m1_subset_1(A_4066,A_4068) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21125])).

tff(c_43137,plain,(
    ! [A_4303,A_4304] :
      ( m1_subset_1(k1_tarski(A_4303),k1_zfmisc_1(A_4304))
      | k1_xboole_0 = A_4304
      | ~ m1_subset_1(A_4303,A_4304)
      | ~ m1_subset_1(A_4303,A_4304)
      | ~ m1_subset_1(A_4303,A_4304)
      | ~ m1_subset_1(A_4303,A_4304)
      | ~ m1_subset_1(A_4303,A_4304)
      | ~ m1_subset_1(A_4303,A_4304)
      | ~ m1_subset_1(A_4303,A_4304)
      | ~ m1_subset_1(A_4303,A_4304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_39760])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_22,plain,(
    ! [A_288] :
      ( r2_hidden('#skF_1'(A_288),A_288)
      | k1_xboole_0 = A_288 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50])).

tff(c_128,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_77,c_116])).

tff(c_626,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_627,plain,(
    ! [B_563,A_564] :
      ( m1_subset_1(u1_struct_0(B_563),k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ m1_pre_topc(B_563,A_564)
      | ~ l1_pre_topc(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20,plain,(
    ! [C_287,B_286,A_285] :
      ( ~ v1_xboole_0(C_287)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(C_287))
      | ~ r2_hidden(A_285,B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_645,plain,(
    ! [A_583,A_584,B_585] :
      ( ~ v1_xboole_0(u1_struct_0(A_583))
      | ~ r2_hidden(A_584,u1_struct_0(B_585))
      | ~ m1_pre_topc(B_585,A_583)
      | ~ l1_pre_topc(A_583) ) ),
    inference(resolution,[status(thm)],[c_627,c_20])).

tff(c_647,plain,(
    ! [A_584,B_585] :
      ( ~ r2_hidden(A_584,u1_struct_0(B_585))
      | ~ m1_pre_topc(B_585,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_626,c_645])).

tff(c_651,plain,(
    ! [A_586,B_587] :
      ( ~ r2_hidden(A_586,u1_struct_0(B_587))
      | ~ m1_pre_topc(B_587,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_647])).

tff(c_657,plain,(
    ! [B_588] :
      ( ~ m1_pre_topc(B_588,'#skF_3')
      | u1_struct_0(B_588) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_651])).

tff(c_661,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_657])).

tff(c_665,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_619])).

tff(c_672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_665])).

tff(c_673,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_618,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_46,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_78,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_621,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) != k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_78])).

tff(c_691,plain,(
    k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) != k2_pre_topc('#skF_3',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_673,c_621])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_58,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_54,plain,(
    v3_borsuk_1('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_72,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_21417,plain,(
    ! [A_2780,C_2781,B_2784,A_2782,B_2783] :
      ( m1_subset_1(k1_enumset1(A_2780,B_2783,C_2781),k1_zfmisc_1(u1_struct_0(A_2782)))
      | ~ m1_pre_topc(B_2784,A_2782)
      | ~ l1_pre_topc(A_2782)
      | u1_struct_0(B_2784) = k1_xboole_0
      | ~ m1_subset_1(C_2781,u1_struct_0(B_2784))
      | ~ m1_subset_1(B_2783,u1_struct_0(B_2784))
      | ~ m1_subset_1(A_2780,u1_struct_0(B_2784)) ) ),
    inference(resolution,[status(thm)],[c_21125,c_28])).

tff(c_21419,plain,(
    ! [A_2780,B_2783,C_2781] :
      ( m1_subset_1(k1_enumset1(A_2780,B_2783,C_2781),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | u1_struct_0('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(C_2781,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_2783,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_2780,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_64,c_21417])).

tff(c_21422,plain,(
    ! [A_2780,B_2783,C_2781] :
      ( m1_subset_1(k1_enumset1(A_2780,B_2783,C_2781),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | u1_struct_0('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(C_2781,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_2783,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_2780,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_21419])).

tff(c_21424,plain,(
    ! [A_2785,B_2786,C_2787] :
      ( m1_subset_1(k1_enumset1(A_2785,B_2786,C_2787),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_2787,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_2786,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_2785,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18501,c_21422])).

tff(c_21600,plain,(
    ! [A_2788,B_2789] :
      ( m1_subset_1(k2_tarski(A_2788,B_2789),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_2789,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_2788,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_2788,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_21424])).

tff(c_21697,plain,(
    ! [A_1] :
      ( m1_subset_1(k1_tarski(A_1),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_21600])).

tff(c_126,plain,
    ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_620,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_895,plain,(
    ! [C_702,A_704,E_706,B_700,G_707,F_701,A_703,D_705,A_699] :
      ( ~ v1_xboole_0(A_704)
      | ~ r2_hidden(A_699,k5_enumset1(A_703,B_700,C_702,D_705,E_706,F_701,G_707))
      | k1_xboole_0 = A_704
      | ~ m1_subset_1(G_707,A_704)
      | ~ m1_subset_1(F_701,A_704)
      | ~ m1_subset_1(E_706,A_704)
      | ~ m1_subset_1(D_705,A_704)
      | ~ m1_subset_1(C_702,A_704)
      | ~ m1_subset_1(B_700,A_704)
      | ~ m1_subset_1(A_703,A_704) ) ),
    inference(resolution,[status(thm)],[c_871,c_20])).

tff(c_902,plain,(
    ! [F_709,A_708,C_715,E_712,B_711,D_714,A_713,A_710] :
      ( ~ v1_xboole_0(A_708)
      | ~ r2_hidden(A_710,k4_enumset1(A_713,B_711,C_715,D_714,E_712,F_709))
      | k1_xboole_0 = A_708
      | ~ m1_subset_1(F_709,A_708)
      | ~ m1_subset_1(E_712,A_708)
      | ~ m1_subset_1(D_714,A_708)
      | ~ m1_subset_1(C_715,A_708)
      | ~ m1_subset_1(B_711,A_708)
      | ~ m1_subset_1(A_713,A_708)
      | ~ m1_subset_1(A_713,A_708) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_895])).

tff(c_936,plain,(
    ! [A_726,C_724,E_729,A_723,B_727,D_728,A_725] :
      ( ~ v1_xboole_0(A_723)
      | ~ r2_hidden(A_725,k3_enumset1(A_726,B_727,C_724,D_728,E_729))
      | k1_xboole_0 = A_723
      | ~ m1_subset_1(E_729,A_723)
      | ~ m1_subset_1(D_728,A_723)
      | ~ m1_subset_1(C_724,A_723)
      | ~ m1_subset_1(B_727,A_723)
      | ~ m1_subset_1(A_726,A_723)
      | ~ m1_subset_1(A_726,A_723)
      | ~ m1_subset_1(A_726,A_723) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_902])).

tff(c_977,plain,(
    ! [A_748,D_746,A_751,B_749,C_750,A_747] :
      ( ~ v1_xboole_0(A_747)
      | ~ r2_hidden(A_748,k2_enumset1(A_751,B_749,C_750,D_746))
      | k1_xboole_0 = A_747
      | ~ m1_subset_1(D_746,A_747)
      | ~ m1_subset_1(C_750,A_747)
      | ~ m1_subset_1(B_749,A_747)
      | ~ m1_subset_1(A_751,A_747)
      | ~ m1_subset_1(A_751,A_747)
      | ~ m1_subset_1(A_751,A_747)
      | ~ m1_subset_1(A_751,A_747) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_936])).

tff(c_984,plain,(
    ! [C_756,A_753,D_752,A_754,B_755] :
      ( ~ v1_xboole_0(A_754)
      | k1_xboole_0 = A_754
      | ~ m1_subset_1(D_752,A_754)
      | ~ m1_subset_1(C_756,A_754)
      | ~ m1_subset_1(B_755,A_754)
      | ~ m1_subset_1(A_753,A_754)
      | k2_enumset1(A_753,B_755,C_756,D_752) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_977])).

tff(c_996,plain,(
    ! [C_756,B_755,A_753] :
      ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) = k1_xboole_0
      | ~ m1_subset_1(C_756,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(B_755,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(A_753,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k2_enumset1(A_753,B_755,C_756,'#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_984])).

tff(c_1008,plain,(
    ! [C_756,B_755,A_753] :
      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) = k1_xboole_0
      | ~ m1_subset_1(C_756,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(B_755,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(A_753,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k2_enumset1(A_753,B_755,C_756,'#skF_5') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_996])).

tff(c_1011,plain,(
    k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_1013,plain,(
    m1_subset_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_56])).

tff(c_1201,plain,(
    ! [C_811,A_812,B_815,G_807,I_809,E_810,D_806,H_813,F_808,B_814] :
      ( m1_subset_1(k6_enumset1(B_814,C_811,D_806,E_810,F_808,G_807,H_813,I_809),k1_zfmisc_1(u1_struct_0(A_812)))
      | ~ m1_pre_topc(B_815,A_812)
      | ~ l1_pre_topc(A_812)
      | u1_struct_0(B_815) = k1_xboole_0
      | ~ m1_subset_1(I_809,u1_struct_0(B_815))
      | ~ m1_subset_1(H_813,u1_struct_0(B_815))
      | ~ m1_subset_1(G_807,u1_struct_0(B_815))
      | ~ m1_subset_1(F_808,u1_struct_0(B_815))
      | ~ m1_subset_1(E_810,u1_struct_0(B_815))
      | ~ m1_subset_1(D_806,u1_struct_0(B_815))
      | ~ m1_subset_1(C_811,u1_struct_0(B_815))
      | ~ m1_subset_1(B_814,u1_struct_0(B_815)) ) ),
    inference(resolution,[status(thm)],[c_812,c_28])).

tff(c_1203,plain,(
    ! [C_811,G_807,I_809,E_810,D_806,H_813,F_808,B_814] :
      ( m1_subset_1(k6_enumset1(B_814,C_811,D_806,E_810,F_808,G_807,H_813,I_809),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | u1_struct_0('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(I_809,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_813,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_807,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_808,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_810,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_806,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_811,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_814,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_64,c_1201])).

tff(c_1206,plain,(
    ! [C_811,G_807,I_809,E_810,D_806,H_813,F_808,B_814] :
      ( m1_subset_1(k6_enumset1(B_814,C_811,D_806,E_810,F_808,G_807,H_813,I_809),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | u1_struct_0('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(I_809,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(H_813,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(G_807,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_808,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_810,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_806,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_811,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_814,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1203])).

tff(c_1245,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1206])).

tff(c_1249,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_619])).

tff(c_1255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1249])).

tff(c_1257,plain,(
    u1_struct_0('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_1596,plain,(
    ! [B_921,F_919,E_922,D_924,A_923,C_925,A_920] :
      ( m1_subset_1(k4_enumset1(A_923,B_921,C_925,D_924,E_922,F_919),k1_zfmisc_1(A_920))
      | k1_xboole_0 = A_920
      | ~ m1_subset_1(F_919,A_920)
      | ~ m1_subset_1(E_922,A_920)
      | ~ m1_subset_1(D_924,A_920)
      | ~ m1_subset_1(C_925,A_920)
      | ~ m1_subset_1(B_921,A_920)
      | ~ m1_subset_1(A_923,A_920)
      | ~ m1_subset_1(A_923,A_920)
      | ~ m1_subset_1(A_923,A_920) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_871])).

tff(c_1696,plain,(
    ! [B_932,C_930,E_934,A_935,D_933,A_931] :
      ( m1_subset_1(k3_enumset1(A_931,B_932,C_930,D_933,E_934),k1_zfmisc_1(A_935))
      | k1_xboole_0 = A_935
      | ~ m1_subset_1(E_934,A_935)
      | ~ m1_subset_1(D_933,A_935)
      | ~ m1_subset_1(C_930,A_935)
      | ~ m1_subset_1(B_932,A_935)
      | ~ m1_subset_1(A_931,A_935)
      | ~ m1_subset_1(A_931,A_935)
      | ~ m1_subset_1(A_931,A_935)
      | ~ m1_subset_1(A_931,A_935) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1596])).

tff(c_1794,plain,(
    ! [C_945,B_944,A_943,D_942,A_946] :
      ( m1_subset_1(k2_enumset1(A_946,B_944,C_945,D_942),k1_zfmisc_1(A_943))
      | k1_xboole_0 = A_943
      | ~ m1_subset_1(D_942,A_943)
      | ~ m1_subset_1(C_945,A_943)
      | ~ m1_subset_1(B_944,A_943)
      | ~ m1_subset_1(A_946,A_943)
      | ~ m1_subset_1(A_946,A_943)
      | ~ m1_subset_1(A_946,A_943)
      | ~ m1_subset_1(A_946,A_943)
      | ~ m1_subset_1(A_946,A_943) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1696])).

tff(c_2019,plain,(
    ! [A_991,B_992,C_993,A_994] :
      ( m1_subset_1(k1_enumset1(A_991,B_992,C_993),k1_zfmisc_1(A_994))
      | k1_xboole_0 = A_994
      | ~ m1_subset_1(C_993,A_994)
      | ~ m1_subset_1(B_992,A_994)
      | ~ m1_subset_1(A_991,A_994)
      | ~ m1_subset_1(A_991,A_994)
      | ~ m1_subset_1(A_991,A_994)
      | ~ m1_subset_1(A_991,A_994)
      | ~ m1_subset_1(A_991,A_994)
      | ~ m1_subset_1(A_991,A_994) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1794])).

tff(c_17065,plain,(
    ! [A_2194,B_2195,A_2196] :
      ( m1_subset_1(k2_tarski(A_2194,B_2195),k1_zfmisc_1(A_2196))
      | k1_xboole_0 = A_2196
      | ~ m1_subset_1(B_2195,A_2196)
      | ~ m1_subset_1(A_2194,A_2196)
      | ~ m1_subset_1(A_2194,A_2196)
      | ~ m1_subset_1(A_2194,A_2196)
      | ~ m1_subset_1(A_2194,A_2196)
      | ~ m1_subset_1(A_2194,A_2196)
      | ~ m1_subset_1(A_2194,A_2196)
      | ~ m1_subset_1(A_2194,A_2196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2019])).

tff(c_17647,plain,(
    ! [A_2247,A_2248] :
      ( m1_subset_1(k1_tarski(A_2247),k1_zfmisc_1(A_2248))
      | k1_xboole_0 = A_2248
      | ~ m1_subset_1(A_2247,A_2248)
      | ~ m1_subset_1(A_2247,A_2248)
      | ~ m1_subset_1(A_2247,A_2248)
      | ~ m1_subset_1(A_2247,A_2248)
      | ~ m1_subset_1(A_2247,A_2248)
      | ~ m1_subset_1(A_2247,A_2248)
      | ~ m1_subset_1(A_2247,A_2248)
      | ~ m1_subset_1(A_2247,A_2248) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_17065])).

tff(c_2130,plain,(
    ! [C_1002,A_1000,B_999,A_1001,B_1003] :
      ( m1_subset_1(k1_enumset1(A_1000,B_999,C_1002),k1_zfmisc_1(u1_struct_0(A_1001)))
      | ~ m1_pre_topc(B_1003,A_1001)
      | ~ l1_pre_topc(A_1001)
      | u1_struct_0(B_1003) = k1_xboole_0
      | ~ m1_subset_1(C_1002,u1_struct_0(B_1003))
      | ~ m1_subset_1(B_999,u1_struct_0(B_1003))
      | ~ m1_subset_1(A_1000,u1_struct_0(B_1003)) ) ),
    inference(resolution,[status(thm)],[c_2019,c_28])).

tff(c_2132,plain,(
    ! [A_1000,B_999,C_1002] :
      ( m1_subset_1(k1_enumset1(A_1000,B_999,C_1002),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | u1_struct_0('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(C_1002,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_999,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1000,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_64,c_2130])).

tff(c_2135,plain,(
    ! [A_1000,B_999,C_1002] :
      ( m1_subset_1(k1_enumset1(A_1000,B_999,C_1002),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | u1_struct_0('#skF_4') = k1_xboole_0
      | ~ m1_subset_1(C_1002,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_999,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1000,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2132])).

tff(c_2137,plain,(
    ! [A_1004,B_1005,C_1006] :
      ( m1_subset_1(k1_enumset1(A_1004,B_1005,C_1006),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_1006,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_1005,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1004,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1257,c_2135])).

tff(c_2259,plain,(
    ! [A_1007,B_1008] :
      ( m1_subset_1(k2_tarski(A_1007,B_1008),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_1008,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1007,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1007,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2137])).

tff(c_2313,plain,(
    ! [A_1] :
      ( m1_subset_1(k1_tarski(A_1),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2259])).

tff(c_2428,plain,(
    ! [A_1021] :
      ( m1_subset_1(k1_tarski(A_1021),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(A_1021,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1021,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_1021,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2259])).

tff(c_2576,plain,(
    ! [A_1027,A_1028] :
      ( m1_subset_1(k1_tarski(A_1027),k1_zfmisc_1(u1_struct_0(A_1028)))
      | ~ m1_pre_topc('#skF_3',A_1028)
      | ~ l1_pre_topc(A_1028)
      | ~ m1_subset_1(A_1027,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2428,c_28])).

tff(c_1050,plain,(
    ! [B_757,A_760,A_761,A_759,C_758] :
      ( ~ v1_xboole_0(A_760)
      | ~ r2_hidden(A_759,k1_enumset1(A_761,B_757,C_758))
      | k1_xboole_0 = A_760
      | ~ m1_subset_1(C_758,A_760)
      | ~ m1_subset_1(B_757,A_760)
      | ~ m1_subset_1(A_761,A_760)
      | ~ m1_subset_1(A_761,A_760)
      | ~ m1_subset_1(A_761,A_760)
      | ~ m1_subset_1(A_761,A_760)
      | ~ m1_subset_1(A_761,A_760) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_977])).

tff(c_1140,plain,(
    ! [A_787,A_788,A_789,B_790] :
      ( ~ v1_xboole_0(A_787)
      | ~ r2_hidden(A_788,k2_tarski(A_789,B_790))
      | k1_xboole_0 = A_787
      | ~ m1_subset_1(B_790,A_787)
      | ~ m1_subset_1(A_789,A_787)
      | ~ m1_subset_1(A_789,A_787)
      | ~ m1_subset_1(A_789,A_787)
      | ~ m1_subset_1(A_789,A_787)
      | ~ m1_subset_1(A_789,A_787)
      | ~ m1_subset_1(A_789,A_787) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1050])).

tff(c_1196,plain,(
    ! [A_803,A_804,A_805] :
      ( ~ v1_xboole_0(A_803)
      | ~ r2_hidden(A_804,k1_tarski(A_805))
      | k1_xboole_0 = A_803
      | ~ m1_subset_1(A_805,A_803)
      | ~ m1_subset_1(A_805,A_803)
      | ~ m1_subset_1(A_805,A_803)
      | ~ m1_subset_1(A_805,A_803)
      | ~ m1_subset_1(A_805,A_803)
      | ~ m1_subset_1(A_805,A_803)
      | ~ m1_subset_1(A_805,A_803) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1140])).

tff(c_1200,plain,(
    ! [A_803,A_805] :
      ( ~ v1_xboole_0(A_803)
      | k1_xboole_0 = A_803
      | ~ m1_subset_1(A_805,A_803)
      | k1_tarski(A_805) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_1196])).

tff(c_2641,plain,(
    ! [A_1028,A_1027] :
      ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_1028)))
      | k1_zfmisc_1(u1_struct_0(A_1028)) = k1_xboole_0
      | k1_tarski(k1_tarski(A_1027)) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_1028)
      | ~ l1_pre_topc(A_1028)
      | ~ m1_subset_1(A_1027,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2576,c_1200])).

tff(c_15935,plain,(
    ! [A_2080] :
      ( k1_tarski(k1_tarski(A_2080)) = k1_xboole_0
      | ~ m1_subset_1(A_2080,u1_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_2641])).

tff(c_15939,plain,(
    k1_tarski(k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_15935])).

tff(c_30,plain,(
    ! [A_313,B_314] :
      ( k6_domain_1(A_313,B_314) = k1_tarski(B_314)
      | ~ m1_subset_1(B_314,A_313)
      | v1_xboole_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1898,plain,(
    ! [A_962,C_964,B_963,D_961,A_960] :
      ( k6_domain_1(k1_zfmisc_1(A_960),k2_enumset1(A_962,B_963,C_964,D_961)) = k1_tarski(k2_enumset1(A_962,B_963,C_964,D_961))
      | v1_xboole_0(k1_zfmisc_1(A_960))
      | k1_xboole_0 = A_960
      | ~ m1_subset_1(D_961,A_960)
      | ~ m1_subset_1(C_964,A_960)
      | ~ m1_subset_1(B_963,A_960)
      | ~ m1_subset_1(A_962,A_960) ) ),
    inference(resolution,[status(thm)],[c_1794,c_30])).

tff(c_1910,plain,(
    ! [A_960,A_4,B_5,C_6] :
      ( k6_domain_1(k1_zfmisc_1(A_960),k1_enumset1(A_4,B_5,C_6)) = k1_tarski(k2_enumset1(A_4,A_4,B_5,C_6))
      | v1_xboole_0(k1_zfmisc_1(A_960))
      | k1_xboole_0 = A_960
      | ~ m1_subset_1(C_6,A_960)
      | ~ m1_subset_1(B_5,A_960)
      | ~ m1_subset_1(A_4,A_960)
      | ~ m1_subset_1(A_4,A_960) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1898])).

tff(c_1916,plain,(
    ! [A_965,A_966,B_967,C_968] :
      ( k6_domain_1(k1_zfmisc_1(A_965),k1_enumset1(A_966,B_967,C_968)) = k1_tarski(k1_enumset1(A_966,B_967,C_968))
      | v1_xboole_0(k1_zfmisc_1(A_965))
      | k1_xboole_0 = A_965
      | ~ m1_subset_1(C_968,A_965)
      | ~ m1_subset_1(B_967,A_965)
      | ~ m1_subset_1(A_966,A_965)
      | ~ m1_subset_1(A_966,A_965) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1910])).

tff(c_1937,plain,(
    ! [A_965,A_2,B_3] :
      ( k6_domain_1(k1_zfmisc_1(A_965),k2_tarski(A_2,B_3)) = k1_tarski(k1_enumset1(A_2,A_2,B_3))
      | v1_xboole_0(k1_zfmisc_1(A_965))
      | k1_xboole_0 = A_965
      | ~ m1_subset_1(B_3,A_965)
      | ~ m1_subset_1(A_2,A_965)
      | ~ m1_subset_1(A_2,A_965)
      | ~ m1_subset_1(A_2,A_965) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1916])).

tff(c_1943,plain,(
    ! [A_969,A_970,B_971] :
      ( k6_domain_1(k1_zfmisc_1(A_969),k2_tarski(A_970,B_971)) = k1_tarski(k2_tarski(A_970,B_971))
      | v1_xboole_0(k1_zfmisc_1(A_969))
      | k1_xboole_0 = A_969
      | ~ m1_subset_1(B_971,A_969)
      | ~ m1_subset_1(A_970,A_969)
      | ~ m1_subset_1(A_970,A_969)
      | ~ m1_subset_1(A_970,A_969) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1937])).

tff(c_1955,plain,(
    ! [A_969,A_1] :
      ( k6_domain_1(k1_zfmisc_1(A_969),k1_tarski(A_1)) = k1_tarski(k2_tarski(A_1,A_1))
      | v1_xboole_0(k1_zfmisc_1(A_969))
      | k1_xboole_0 = A_969
      | ~ m1_subset_1(A_1,A_969)
      | ~ m1_subset_1(A_1,A_969)
      | ~ m1_subset_1(A_1,A_969)
      | ~ m1_subset_1(A_1,A_969) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1943])).

tff(c_1959,plain,(
    ! [A_969,A_1] :
      ( k6_domain_1(k1_zfmisc_1(A_969),k1_tarski(A_1)) = k1_tarski(k1_tarski(A_1))
      | v1_xboole_0(k1_zfmisc_1(A_969))
      | k1_xboole_0 = A_969
      | ~ m1_subset_1(A_1,A_969)
      | ~ m1_subset_1(A_1,A_969)
      | ~ m1_subset_1(A_1,A_969)
      | ~ m1_subset_1(A_1,A_969) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1955])).

tff(c_15960,plain,(
    ! [A_969] :
      ( k6_domain_1(k1_zfmisc_1(A_969),k1_xboole_0) = k1_tarski(k1_tarski(k1_tarski('#skF_6')))
      | v1_xboole_0(k1_zfmisc_1(A_969))
      | k1_xboole_0 = A_969
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_969)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_969)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_969)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_969) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15939,c_1959])).

tff(c_16298,plain,(
    ! [A_2132] :
      ( k6_domain_1(k1_zfmisc_1(A_2132),k1_xboole_0) = k1_tarski(k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_2132))
      | k1_xboole_0 = A_2132
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_2132)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_2132)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_2132)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_2132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15939,c_15960])).

tff(c_16304,plain,
    ( k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))),k1_xboole_0) = k1_tarski(k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | k1_zfmisc_1(u1_struct_0('#skF_3')) = k1_xboole_0
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2313,c_16298])).

tff(c_16310,plain,
    ( k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))),k1_xboole_0) = k1_tarski(k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | k1_zfmisc_1(u1_struct_0('#skF_3')) = k1_xboole_0
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16304])).

tff(c_16311,plain,(
    ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_16310])).

tff(c_16317,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2313,c_16311])).

tff(c_16324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16317])).

tff(c_16326,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_16310])).

tff(c_44,plain,(
    ! [A_331,B_347,C_355,E_361] :
      ( k8_relset_1(u1_struct_0(A_331),u1_struct_0(B_347),C_355,E_361) = k2_pre_topc(A_331,E_361)
      | ~ m1_subset_1(E_361,k1_zfmisc_1(u1_struct_0(A_331)))
      | ~ m1_subset_1(E_361,k1_zfmisc_1(u1_struct_0(B_347)))
      | ~ v3_borsuk_1(C_355,A_331,B_347)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_331),u1_struct_0(B_347))))
      | ~ v5_pre_topc(C_355,A_331,B_347)
      | ~ v1_funct_2(C_355,u1_struct_0(A_331),u1_struct_0(B_347))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc(B_347,A_331)
      | ~ v4_tex_2(B_347,A_331)
      | v2_struct_0(B_347)
      | ~ l1_pre_topc(A_331)
      | ~ v3_tdlat_3(A_331)
      | ~ v2_pre_topc(A_331)
      | v2_struct_0(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_16400,plain,(
    ! [B_347,C_355] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_347),C_355,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_347)))
      | ~ v3_borsuk_1(C_355,'#skF_3',B_347)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(C_355,'#skF_3',B_347)
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0(B_347))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc(B_347,'#skF_3')
      | ~ v4_tex_2(B_347,'#skF_3')
      | v2_struct_0(B_347)
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16326,c_44])).

tff(c_16470,plain,(
    ! [B_347,C_355] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_347),C_355,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_347)))
      | ~ v3_borsuk_1(C_355,'#skF_3',B_347)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(C_355,'#skF_3',B_347)
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0(B_347))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc(B_347,'#skF_3')
      | ~ v4_tex_2(B_347,'#skF_3')
      | v2_struct_0(B_347)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_16400])).

tff(c_16482,plain,(
    ! [B_2136,C_2137] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_2136),C_2137,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_2136)))
      | ~ v3_borsuk_1(C_2137,'#skF_3',B_2136)
      | ~ m1_subset_1(C_2137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_2136))))
      | ~ v5_pre_topc(C_2137,'#skF_3',B_2136)
      | ~ v1_funct_2(C_2137,u1_struct_0('#skF_3'),u1_struct_0(B_2136))
      | ~ v1_funct_1(C_2137)
      | ~ m1_pre_topc(B_2136,'#skF_3')
      | ~ v4_tex_2(B_2136,'#skF_3')
      | v2_struct_0(B_2136) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_16470])).

tff(c_16501,plain,(
    ! [C_2137] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),C_2137,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_borsuk_1(C_2137,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_2137,k1_xboole_0)
      | ~ v5_pre_topc(C_2137,'#skF_3','#skF_4')
      | ~ v1_funct_2(C_2137,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_2137)
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ v4_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1011,c_16482])).

tff(c_16515,plain,(
    ! [C_2137] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),C_2137,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_borsuk_1(C_2137,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_2137,k1_xboole_0)
      | ~ v5_pre_topc(C_2137,'#skF_3','#skF_4')
      | ~ v1_funct_2(C_2137,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_2137)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_16501])).

tff(c_16516,plain,(
    ! [C_2137] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),C_2137,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_borsuk_1(C_2137,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_2137,k1_xboole_0)
      | ~ v5_pre_topc(C_2137,'#skF_3','#skF_4')
      | ~ v1_funct_2(C_2137,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_2137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_16515])).

tff(c_16716,plain,(
    ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_16516])).

tff(c_17665,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_17647,c_16716])).

tff(c_17760,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_17665])).

tff(c_17762,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1257,c_17760])).

tff(c_17764,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_16516])).

tff(c_2471,plain,(
    ! [B_347,C_355,A_1021] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_347),C_355,k1_tarski(A_1021)) = k2_pre_topc('#skF_3',k1_tarski(A_1021))
      | ~ m1_subset_1(k1_tarski(A_1021),k1_zfmisc_1(u1_struct_0(B_347)))
      | ~ v3_borsuk_1(C_355,'#skF_3',B_347)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(C_355,'#skF_3',B_347)
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0(B_347))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc(B_347,'#skF_3')
      | ~ v4_tex_2(B_347,'#skF_3')
      | v2_struct_0(B_347)
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(A_1021,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2428,c_44])).

tff(c_2530,plain,(
    ! [B_347,C_355,A_1021] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_347),C_355,k1_tarski(A_1021)) = k2_pre_topc('#skF_3',k1_tarski(A_1021))
      | ~ m1_subset_1(k1_tarski(A_1021),k1_zfmisc_1(u1_struct_0(B_347)))
      | ~ v3_borsuk_1(C_355,'#skF_3',B_347)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(C_355,'#skF_3',B_347)
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0(B_347))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc(B_347,'#skF_3')
      | ~ v4_tex_2(B_347,'#skF_3')
      | v2_struct_0(B_347)
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(A_1021,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_2471])).

tff(c_2531,plain,(
    ! [B_347,C_355,A_1021] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_347),C_355,k1_tarski(A_1021)) = k2_pre_topc('#skF_3',k1_tarski(A_1021))
      | ~ m1_subset_1(k1_tarski(A_1021),k1_zfmisc_1(u1_struct_0(B_347)))
      | ~ v3_borsuk_1(C_355,'#skF_3',B_347)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(C_355,'#skF_3',B_347)
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0(B_347))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc(B_347,'#skF_3')
      | ~ v4_tex_2(B_347,'#skF_3')
      | v2_struct_0(B_347)
      | ~ m1_subset_1(A_1021,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2530])).

tff(c_17770,plain,(
    ! [C_355] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),C_355,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ v3_borsuk_1(C_355,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v5_pre_topc(C_355,'#skF_3','#skF_4')
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ v4_tex_2('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_17764,c_2531])).

tff(c_17830,plain,(
    ! [C_355] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),C_355,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ v3_borsuk_1(C_355,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_355,k1_xboole_0)
      | ~ v5_pre_topc(C_355,'#skF_3','#skF_4')
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_355)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_66,c_64,c_1011,c_17770])).

tff(c_18059,plain,(
    ! [C_2257] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),C_2257,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ v3_borsuk_1(C_2257,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_2257,k1_xboole_0)
      | ~ v5_pre_topc(C_2257,'#skF_3','#skF_4')
      | ~ v1_funct_2(C_2257,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_2257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_17830])).

tff(c_18065,plain,
    ( ~ v3_borsuk_1('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_xboole_0)
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18059,c_691])).

tff(c_18073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1013,c_54,c_18065])).

tff(c_18075,plain,(
    k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_909,plain,(
    ! [A_716,F_722,A_717,E_719,C_718,D_721,B_720] :
      ( ~ v1_xboole_0(A_717)
      | k1_xboole_0 = A_717
      | ~ m1_subset_1(F_722,A_717)
      | ~ m1_subset_1(E_719,A_717)
      | ~ m1_subset_1(D_721,A_717)
      | ~ m1_subset_1(C_718,A_717)
      | ~ m1_subset_1(B_720,A_717)
      | ~ m1_subset_1(A_716,A_717)
      | k4_enumset1(A_716,B_720,C_718,D_721,E_719,F_722) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_902])).

tff(c_921,plain,(
    ! [A_716,E_719,C_718,D_721,B_720] :
      ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) = k1_xboole_0
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(D_721,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(C_718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(B_720,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(A_716,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k4_enumset1(A_716,B_720,C_718,D_721,E_719,'#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_909])).

tff(c_933,plain,(
    ! [A_716,E_719,C_718,D_721,B_720] :
      ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) = k1_xboole_0
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(D_721,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(C_718,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(B_720,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(A_716,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k4_enumset1(A_716,B_720,C_718,D_721,E_719,'#skF_5') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_921])).

tff(c_18543,plain,(
    ! [B_2382,A_2381,E_2384,D_2383,C_2385] :
      ( ~ m1_subset_1(E_2384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(D_2383,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(C_2385,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(B_2382,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(A_2381,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k4_enumset1(A_2381,B_2382,C_2385,D_2383,E_2384,'#skF_5') = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_18075,c_933])).

tff(c_18694,plain,(
    ! [D_2436,C_2437,B_2438,A_2439] :
      ( ~ m1_subset_1(D_2436,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(C_2437,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(B_2438,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(A_2439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k4_enumset1(A_2439,B_2438,C_2437,D_2436,'#skF_5','#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_18543])).

tff(c_18706,plain,(
    ! [C_2440,B_2441,A_2442] :
      ( ~ m1_subset_1(C_2440,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(B_2441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(A_2442,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k4_enumset1(A_2442,B_2441,C_2440,'#skF_5','#skF_5','#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_18694])).

tff(c_18718,plain,(
    ! [B_2443,A_2444] :
      ( ~ m1_subset_1(B_2443,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ m1_subset_1(A_2444,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k4_enumset1(A_2444,B_2443,'#skF_5','#skF_5','#skF_5','#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_18706])).

tff(c_18730,plain,(
    ! [A_2445] :
      ( ~ m1_subset_1(A_2445,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | k4_enumset1(A_2445,'#skF_5','#skF_5','#skF_5','#skF_5','#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_18718])).

tff(c_18744,plain,(
    k4_enumset1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_5','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_18730])).

tff(c_18910,plain,(
    ! [A_2458] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2458))
      | k1_xboole_0 = A_2458
      | ~ m1_subset_1('#skF_5',A_2458)
      | ~ m1_subset_1('#skF_5',A_2458)
      | ~ m1_subset_1('#skF_5',A_2458)
      | ~ m1_subset_1('#skF_5',A_2458)
      | ~ m1_subset_1('#skF_5',A_2458)
      | ~ m1_subset_1('#skF_5',A_2458)
      | ~ m1_subset_1('#skF_5',A_2458)
      | ~ m1_subset_1('#skF_5',A_2458) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18744,c_18760])).

tff(c_18176,plain,(
    ! [A_2277,A_2278,C_2275,B_2274,A_2276] :
      ( ~ v1_xboole_0(A_2277)
      | ~ r2_hidden(A_2276,k1_enumset1(A_2278,B_2274,C_2275))
      | k1_xboole_0 = A_2277
      | ~ m1_subset_1(C_2275,A_2277)
      | ~ m1_subset_1(B_2274,A_2277)
      | ~ m1_subset_1(A_2278,A_2277)
      | ~ m1_subset_1(A_2278,A_2277)
      | ~ m1_subset_1(A_2278,A_2277)
      | ~ m1_subset_1(A_2278,A_2277)
      | ~ m1_subset_1(A_2278,A_2277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_977])).

tff(c_18297,plain,(
    ! [A_2312,A_2313,A_2314,B_2315] :
      ( ~ v1_xboole_0(A_2312)
      | ~ r2_hidden(A_2313,k2_tarski(A_2314,B_2315))
      | k1_xboole_0 = A_2312
      | ~ m1_subset_1(B_2315,A_2312)
      | ~ m1_subset_1(A_2314,A_2312)
      | ~ m1_subset_1(A_2314,A_2312)
      | ~ m1_subset_1(A_2314,A_2312)
      | ~ m1_subset_1(A_2314,A_2312)
      | ~ m1_subset_1(A_2314,A_2312)
      | ~ m1_subset_1(A_2314,A_2312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_18176])).

tff(c_18427,plain,(
    ! [A_2339,A_2340,A_2341] :
      ( ~ v1_xboole_0(A_2339)
      | ~ r2_hidden(A_2340,k1_tarski(A_2341))
      | k1_xboole_0 = A_2339
      | ~ m1_subset_1(A_2341,A_2339)
      | ~ m1_subset_1(A_2341,A_2339)
      | ~ m1_subset_1(A_2341,A_2339)
      | ~ m1_subset_1(A_2341,A_2339)
      | ~ m1_subset_1(A_2341,A_2339)
      | ~ m1_subset_1(A_2341,A_2339)
      | ~ m1_subset_1(A_2341,A_2339) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_18297])).

tff(c_18433,plain,(
    ! [A_2339,A_2341] :
      ( ~ v1_xboole_0(A_2339)
      | k1_xboole_0 = A_2339
      | ~ m1_subset_1(A_2341,A_2339)
      | k1_tarski(A_2341) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_18427])).

tff(c_19030,plain,(
    ! [A_2458] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_2458))
      | k1_zfmisc_1(A_2458) = k1_xboole_0
      | k1_tarski(k1_xboole_0) = k1_xboole_0
      | k1_xboole_0 = A_2458
      | ~ m1_subset_1('#skF_5',A_2458) ) ),
    inference(resolution,[status(thm)],[c_18910,c_18433])).

tff(c_19056,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_19030])).

tff(c_21806,plain,(
    ! [A_2793] :
      ( m1_subset_1(k1_tarski(A_2793),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(A_2793,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_2793,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_2793,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_21600])).

tff(c_22030,plain,(
    ! [A_2796,A_2797] :
      ( m1_subset_1(k1_tarski(A_2796),k1_zfmisc_1(u1_struct_0(A_2797)))
      | ~ m1_pre_topc('#skF_3',A_2797)
      | ~ l1_pre_topc(A_2797)
      | ~ m1_subset_1(A_2796,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_21806,c_28])).

tff(c_22153,plain,(
    ! [A_2797,A_2796] :
      ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_2797)))
      | k1_zfmisc_1(u1_struct_0(A_2797)) = k1_xboole_0
      | k1_tarski(k1_tarski(A_2796)) = k1_xboole_0
      | ~ m1_pre_topc('#skF_3',A_2797)
      | ~ l1_pre_topc(A_2797)
      | ~ m1_subset_1(A_2796,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_22030,c_18433])).

tff(c_36895,plain,(
    ! [A_3837] :
      ( k1_tarski(k1_tarski(A_3837)) = k1_xboole_0
      | ~ m1_subset_1(A_3837,u1_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_22153])).

tff(c_36899,plain,(
    k1_tarski(k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_36895])).

tff(c_20602,plain,(
    ! [B_2691,C_2689,D_2690,A_2693,A_2692] :
      ( k6_domain_1(k1_zfmisc_1(A_2693),k2_enumset1(A_2692,B_2691,C_2689,D_2690)) = k1_tarski(k2_enumset1(A_2692,B_2691,C_2689,D_2690))
      | v1_xboole_0(k1_zfmisc_1(A_2693))
      | k1_xboole_0 = A_2693
      | ~ m1_subset_1(D_2690,A_2693)
      | ~ m1_subset_1(C_2689,A_2693)
      | ~ m1_subset_1(B_2691,A_2693)
      | ~ m1_subset_1(A_2692,A_2693) ) ),
    inference(resolution,[status(thm)],[c_20377,c_30])).

tff(c_20614,plain,(
    ! [A_2693,A_4,B_5,C_6] :
      ( k6_domain_1(k1_zfmisc_1(A_2693),k1_enumset1(A_4,B_5,C_6)) = k1_tarski(k2_enumset1(A_4,A_4,B_5,C_6))
      | v1_xboole_0(k1_zfmisc_1(A_2693))
      | k1_xboole_0 = A_2693
      | ~ m1_subset_1(C_6,A_2693)
      | ~ m1_subset_1(B_5,A_2693)
      | ~ m1_subset_1(A_4,A_2693)
      | ~ m1_subset_1(A_4,A_2693) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_20602])).

tff(c_20620,plain,(
    ! [A_2694,A_2695,B_2696,C_2697] :
      ( k6_domain_1(k1_zfmisc_1(A_2694),k1_enumset1(A_2695,B_2696,C_2697)) = k1_tarski(k1_enumset1(A_2695,B_2696,C_2697))
      | v1_xboole_0(k1_zfmisc_1(A_2694))
      | k1_xboole_0 = A_2694
      | ~ m1_subset_1(C_2697,A_2694)
      | ~ m1_subset_1(B_2696,A_2694)
      | ~ m1_subset_1(A_2695,A_2694)
      | ~ m1_subset_1(A_2695,A_2694) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_20614])).

tff(c_20641,plain,(
    ! [A_2694,A_2,B_3] :
      ( k6_domain_1(k1_zfmisc_1(A_2694),k2_tarski(A_2,B_3)) = k1_tarski(k1_enumset1(A_2,A_2,B_3))
      | v1_xboole_0(k1_zfmisc_1(A_2694))
      | k1_xboole_0 = A_2694
      | ~ m1_subset_1(B_3,A_2694)
      | ~ m1_subset_1(A_2,A_2694)
      | ~ m1_subset_1(A_2,A_2694)
      | ~ m1_subset_1(A_2,A_2694) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_20620])).

tff(c_20647,plain,(
    ! [A_2698,A_2699,B_2700] :
      ( k6_domain_1(k1_zfmisc_1(A_2698),k2_tarski(A_2699,B_2700)) = k1_tarski(k2_tarski(A_2699,B_2700))
      | v1_xboole_0(k1_zfmisc_1(A_2698))
      | k1_xboole_0 = A_2698
      | ~ m1_subset_1(B_2700,A_2698)
      | ~ m1_subset_1(A_2699,A_2698)
      | ~ m1_subset_1(A_2699,A_2698)
      | ~ m1_subset_1(A_2699,A_2698) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20641])).

tff(c_20665,plain,(
    ! [A_2698,A_1] :
      ( k6_domain_1(k1_zfmisc_1(A_2698),k1_tarski(A_1)) = k1_tarski(k2_tarski(A_1,A_1))
      | v1_xboole_0(k1_zfmisc_1(A_2698))
      | k1_xboole_0 = A_2698
      | ~ m1_subset_1(A_1,A_2698)
      | ~ m1_subset_1(A_1,A_2698)
      | ~ m1_subset_1(A_1,A_2698)
      | ~ m1_subset_1(A_1,A_2698) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_20647])).

tff(c_20669,plain,(
    ! [A_2698,A_1] :
      ( k6_domain_1(k1_zfmisc_1(A_2698),k1_tarski(A_1)) = k1_tarski(k1_tarski(A_1))
      | v1_xboole_0(k1_zfmisc_1(A_2698))
      | k1_xboole_0 = A_2698
      | ~ m1_subset_1(A_1,A_2698)
      | ~ m1_subset_1(A_1,A_2698)
      | ~ m1_subset_1(A_1,A_2698)
      | ~ m1_subset_1(A_1,A_2698) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_20665])).

tff(c_36918,plain,(
    ! [A_2698] :
      ( k6_domain_1(k1_zfmisc_1(A_2698),k1_xboole_0) = k1_tarski(k1_tarski(k1_tarski('#skF_6')))
      | v1_xboole_0(k1_zfmisc_1(A_2698))
      | k1_xboole_0 = A_2698
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_2698)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_2698)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_2698)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_2698) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36899,c_20669])).

tff(c_37410,plain,(
    ! [A_3884] :
      ( k6_domain_1(k1_zfmisc_1(A_3884),k1_xboole_0) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_3884))
      | k1_xboole_0 = A_3884
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_3884)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_3884)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_3884)
      | ~ m1_subset_1(k1_tarski('#skF_6'),A_3884) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19056,c_36899,c_36918])).

tff(c_37416,plain,
    ( k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))),k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | k1_zfmisc_1(u1_struct_0('#skF_3')) = k1_xboole_0
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_21697,c_37410])).

tff(c_37422,plain,
    ( k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))),k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | k1_zfmisc_1(u1_struct_0('#skF_3')) = k1_xboole_0
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_37416])).

tff(c_37444,plain,(
    ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_37422])).

tff(c_37450,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_21697,c_37444])).

tff(c_37457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_37450])).

tff(c_37459,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_37422])).

tff(c_37538,plain,(
    ! [B_347,C_355] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_347),C_355,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_347)))
      | ~ v3_borsuk_1(C_355,'#skF_3',B_347)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(C_355,'#skF_3',B_347)
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0(B_347))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc(B_347,'#skF_3')
      | ~ v4_tex_2(B_347,'#skF_3')
      | v2_struct_0(B_347)
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_37459,c_44])).

tff(c_37621,plain,(
    ! [B_347,C_355] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_347),C_355,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_347)))
      | ~ v3_borsuk_1(C_355,'#skF_3',B_347)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_347))))
      | ~ v5_pre_topc(C_355,'#skF_3',B_347)
      | ~ v1_funct_2(C_355,u1_struct_0('#skF_3'),u1_struct_0(B_347))
      | ~ v1_funct_1(C_355)
      | ~ m1_pre_topc(B_347,'#skF_3')
      | ~ v4_tex_2(B_347,'#skF_3')
      | v2_struct_0(B_347)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_37538])).

tff(c_37814,plain,(
    ! [B_3897,C_3898] :
      ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_3897),C_3898,k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_3897)))
      | ~ v3_borsuk_1(C_3898,'#skF_3',B_3897)
      | ~ m1_subset_1(C_3898,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_3897))))
      | ~ v5_pre_topc(C_3898,'#skF_3',B_3897)
      | ~ v1_funct_2(C_3898,u1_struct_0('#skF_3'),u1_struct_0(B_3897))
      | ~ v1_funct_1(C_3898)
      | ~ m1_pre_topc(B_3897,'#skF_3')
      | ~ v4_tex_2(B_3897,'#skF_3')
      | v2_struct_0(B_3897) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_37621])).

tff(c_37845,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ v3_borsuk_1('#skF_5','#skF_3','#skF_4')
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v4_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_37814])).

tff(c_37855,plain,
    ( k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_tarski('#skF_6')) = k2_pre_topc('#skF_3',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_58,c_54,c_37845])).

tff(c_37856,plain,(
    ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_691,c_37855])).

tff(c_43251,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_43137,c_37856])).

tff(c_43510,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_43251])).

tff(c_43512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18501,c_43510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:08 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.10/13.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.10/13.20  
% 23.10/13.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.10/13.20  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k4_mcart_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 23.10/13.20  
% 23.10/13.20  %Foreground sorts:
% 23.10/13.20  
% 23.10/13.20  
% 23.10/13.20  %Background operators:
% 23.10/13.20  
% 23.10/13.20  
% 23.10/13.20  %Foreground operators:
% 23.10/13.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 23.10/13.20  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 23.10/13.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.10/13.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.10/13.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.10/13.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 23.10/13.20  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 23.10/13.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.10/13.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.10/13.20  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 23.10/13.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.10/13.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 23.10/13.20  tff('#skF_7', type, '#skF_7': $i).
% 23.10/13.20  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 23.10/13.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.10/13.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.10/13.20  tff('#skF_5', type, '#skF_5': $i).
% 23.10/13.20  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 23.10/13.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.10/13.20  tff('#skF_6', type, '#skF_6': $i).
% 23.10/13.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.10/13.20  tff('#skF_3', type, '#skF_3': $i).
% 23.10/13.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.10/13.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.10/13.20  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 23.10/13.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 23.10/13.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.10/13.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.10/13.20  tff('#skF_4', type, '#skF_4': $i).
% 23.10/13.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.10/13.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 23.10/13.20  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 23.10/13.20  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 23.10/13.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 23.10/13.20  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 23.10/13.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.10/13.20  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 23.10/13.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.10/13.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 23.10/13.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.10/13.20  
% 23.30/13.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 23.30/13.24  tff(f_224, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 23.30/13.24  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, A) => (![I]: (m1_subset_1(I, A) => (~(A = k1_xboole_0) => m1_subset_1(k6_enumset1(B, C, D, E, F, G, H, I), k1_zfmisc_1(A))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_subset_1)).
% 23.30/13.24  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 23.30/13.24  tff(f_108, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 23.30/13.24  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 23.30/13.24  tff(f_132, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 23.30/13.24  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 23.30/13.24  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 23.30/13.24  tff(f_30, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 23.30/13.24  tff(f_32, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 23.30/13.24  tff(f_34, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 23.30/13.24  tff(f_36, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 23.30/13.24  tff(f_38, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 23.30/13.24  tff(f_40, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 23.30/13.24  tff(f_91, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 23.30/13.24  tff(f_75, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 23.30/13.24  tff(f_185, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 23.30/13.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 23.30/13.24  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_812, plain, (![F_676, I_675, C_670, H_673, D_669, E_674, G_668, A_672, B_671]: (m1_subset_1(k6_enumset1(B_671, C_670, D_669, E_674, F_676, G_668, H_673, I_675), k1_zfmisc_1(A_672)) | k1_xboole_0=A_672 | ~m1_subset_1(I_675, A_672) | ~m1_subset_1(H_673, A_672) | ~m1_subset_1(G_668, A_672) | ~m1_subset_1(F_676, A_672) | ~m1_subset_1(E_674, A_672) | ~m1_subset_1(D_669, A_672) | ~m1_subset_1(C_670, A_672) | ~m1_subset_1(B_671, A_672))), inference(cnfTransformation, [status(thm)], [f_68])).
% 23.30/13.24  tff(c_28, plain, (![C_312, A_306, B_310]: (m1_subset_1(C_312, k1_zfmisc_1(u1_struct_0(A_306))) | ~m1_subset_1(C_312, k1_zfmisc_1(u1_struct_0(B_310))) | ~m1_pre_topc(B_310, A_306) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_101])).
% 23.30/13.24  tff(c_18185, plain, (![A_2285, B_2288, B_2287, G_2280, F_2281, D_2279, E_2283, I_2282, H_2286, C_2284]: (m1_subset_1(k6_enumset1(B_2287, C_2284, D_2279, E_2283, F_2281, G_2280, H_2286, I_2282), k1_zfmisc_1(u1_struct_0(A_2285))) | ~m1_pre_topc(B_2288, A_2285) | ~l1_pre_topc(A_2285) | u1_struct_0(B_2288)=k1_xboole_0 | ~m1_subset_1(I_2282, u1_struct_0(B_2288)) | ~m1_subset_1(H_2286, u1_struct_0(B_2288)) | ~m1_subset_1(G_2280, u1_struct_0(B_2288)) | ~m1_subset_1(F_2281, u1_struct_0(B_2288)) | ~m1_subset_1(E_2283, u1_struct_0(B_2288)) | ~m1_subset_1(D_2279, u1_struct_0(B_2288)) | ~m1_subset_1(C_2284, u1_struct_0(B_2288)) | ~m1_subset_1(B_2287, u1_struct_0(B_2288)))), inference(resolution, [status(thm)], [c_812, c_28])).
% 23.30/13.24  tff(c_18187, plain, (![B_2287, G_2280, F_2281, D_2279, E_2283, I_2282, H_2286, C_2284]: (m1_subset_1(k6_enumset1(B_2287, C_2284, D_2279, E_2283, F_2281, G_2280, H_2286, I_2282), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1(I_2282, u1_struct_0('#skF_4')) | ~m1_subset_1(H_2286, u1_struct_0('#skF_4')) | ~m1_subset_1(G_2280, u1_struct_0('#skF_4')) | ~m1_subset_1(F_2281, u1_struct_0('#skF_4')) | ~m1_subset_1(E_2283, u1_struct_0('#skF_4')) | ~m1_subset_1(D_2279, u1_struct_0('#skF_4')) | ~m1_subset_1(C_2284, u1_struct_0('#skF_4')) | ~m1_subset_1(B_2287, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_64, c_18185])).
% 23.30/13.24  tff(c_18190, plain, (![B_2287, G_2280, F_2281, D_2279, E_2283, I_2282, H_2286, C_2284]: (m1_subset_1(k6_enumset1(B_2287, C_2284, D_2279, E_2283, F_2281, G_2280, H_2286, I_2282), k1_zfmisc_1(u1_struct_0('#skF_3'))) | u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1(I_2282, u1_struct_0('#skF_4')) | ~m1_subset_1(H_2286, u1_struct_0('#skF_4')) | ~m1_subset_1(G_2280, u1_struct_0('#skF_4')) | ~m1_subset_1(F_2281, u1_struct_0('#skF_4')) | ~m1_subset_1(E_2283, u1_struct_0('#skF_4')) | ~m1_subset_1(D_2279, u1_struct_0('#skF_4')) | ~m1_subset_1(C_2284, u1_struct_0('#skF_4')) | ~m1_subset_1(B_2287, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18187])).
% 23.30/13.24  tff(c_18477, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_18190])).
% 23.30/13.24  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_74, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_66, plain, (v4_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_116, plain, (![A_398, B_399]: (k6_domain_1(A_398, B_399)=k1_tarski(B_399) | ~m1_subset_1(B_399, A_398) | v1_xboole_0(A_398))), inference(cnfTransformation, [status(thm)], [f_108])).
% 23.30/13.24  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_116])).
% 23.30/13.24  tff(c_138, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_127])).
% 23.30/13.24  tff(c_32, plain, (![B_317, A_315]: (m1_subset_1(u1_struct_0(B_317), k1_zfmisc_1(u1_struct_0(A_315))) | ~m1_pre_topc(B_317, A_315) | ~l1_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_115])).
% 23.30/13.24  tff(c_590, plain, (![B_556, A_557]: (v3_tex_2(u1_struct_0(B_556), A_557) | ~m1_subset_1(u1_struct_0(B_556), k1_zfmisc_1(u1_struct_0(A_557))) | ~v4_tex_2(B_556, A_557) | ~m1_pre_topc(B_556, A_557) | ~l1_pre_topc(A_557) | v2_struct_0(A_557))), inference(cnfTransformation, [status(thm)], [f_132])).
% 23.30/13.24  tff(c_595, plain, (![B_558, A_559]: (v3_tex_2(u1_struct_0(B_558), A_559) | ~v4_tex_2(B_558, A_559) | v2_struct_0(A_559) | ~m1_pre_topc(B_558, A_559) | ~l1_pre_topc(A_559))), inference(resolution, [status(thm)], [c_32, c_590])).
% 23.30/13.24  tff(c_534, plain, (![B_533, A_534]: (~v3_tex_2(B_533, A_534) | ~m1_subset_1(B_533, k1_zfmisc_1(u1_struct_0(A_534))) | ~v1_xboole_0(B_533) | ~l1_pre_topc(A_534) | ~v2_pre_topc(A_534) | v2_struct_0(A_534))), inference(cnfTransformation, [status(thm)], [f_147])).
% 23.30/13.24  tff(c_538, plain, (![B_317, A_315]: (~v3_tex_2(u1_struct_0(B_317), A_315) | ~v1_xboole_0(u1_struct_0(B_317)) | ~v2_pre_topc(A_315) | v2_struct_0(A_315) | ~m1_pre_topc(B_317, A_315) | ~l1_pre_topc(A_315))), inference(resolution, [status(thm)], [c_32, c_534])).
% 23.30/13.24  tff(c_600, plain, (![B_560, A_561]: (~v1_xboole_0(u1_struct_0(B_560)) | ~v2_pre_topc(A_561) | ~v4_tex_2(B_560, A_561) | v2_struct_0(A_561) | ~m1_pre_topc(B_560, A_561) | ~l1_pre_topc(A_561))), inference(resolution, [status(thm)], [c_595, c_538])).
% 23.30/13.24  tff(c_604, plain, (![A_562]: (~v2_pre_topc(A_562) | ~v4_tex_2('#skF_4', A_562) | v2_struct_0(A_562) | ~m1_pre_topc('#skF_4', A_562) | ~l1_pre_topc(A_562))), inference(resolution, [status(thm)], [c_138, c_600])).
% 23.30/13.24  tff(c_611, plain, (~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_604])).
% 23.30/13.24  tff(c_615, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_74, c_611])).
% 23.30/13.24  tff(c_617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_615])).
% 23.30/13.24  tff(c_619, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_127])).
% 23.30/13.24  tff(c_18492, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18477, c_619])).
% 23.30/13.24  tff(c_18499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_18492])).
% 23.30/13.24  tff(c_18501, plain, (u1_struct_0('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_18190])).
% 23.30/13.24  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 23.30/13.24  tff(c_6, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 23.30/13.24  tff(c_8, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.30/13.24  tff(c_10, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 23.30/13.24  tff(c_12, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.30/13.24  tff(c_14, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 23.30/13.24  tff(c_16, plain, (![G_28, E_26, F_27, A_22, B_23, D_25, C_24]: (k6_enumset1(A_22, A_22, B_23, C_24, D_25, E_26, F_27, G_28)=k5_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.30/13.24  tff(c_871, plain, (![A_691, A_696, F_694, D_697, C_692, E_693, B_698, G_695]: (m1_subset_1(k5_enumset1(A_691, B_698, C_692, D_697, E_693, F_694, G_695), k1_zfmisc_1(A_696)) | k1_xboole_0=A_696 | ~m1_subset_1(G_695, A_696) | ~m1_subset_1(F_694, A_696) | ~m1_subset_1(E_693, A_696) | ~m1_subset_1(D_697, A_696) | ~m1_subset_1(C_692, A_696) | ~m1_subset_1(B_698, A_696) | ~m1_subset_1(A_691, A_696) | ~m1_subset_1(A_691, A_696))), inference(superposition, [status(thm), theory('equality')], [c_16, c_812])).
% 23.30/13.24  tff(c_18760, plain, (![C_2457, B_2453, A_2455, D_2456, F_2451, E_2454, A_2452]: (m1_subset_1(k4_enumset1(A_2455, B_2453, C_2457, D_2456, E_2454, F_2451), k1_zfmisc_1(A_2452)) | k1_xboole_0=A_2452 | ~m1_subset_1(F_2451, A_2452) | ~m1_subset_1(E_2454, A_2452) | ~m1_subset_1(D_2456, A_2452) | ~m1_subset_1(C_2457, A_2452) | ~m1_subset_1(B_2453, A_2452) | ~m1_subset_1(A_2455, A_2452) | ~m1_subset_1(A_2455, A_2452) | ~m1_subset_1(A_2455, A_2452))), inference(superposition, [status(thm), theory('equality')], [c_14, c_871])).
% 23.30/13.24  tff(c_20153, plain, (![C_2668, A_2669, B_2670, A_2667, D_2671, E_2672]: (m1_subset_1(k3_enumset1(A_2669, B_2670, C_2668, D_2671, E_2672), k1_zfmisc_1(A_2667)) | k1_xboole_0=A_2667 | ~m1_subset_1(E_2672, A_2667) | ~m1_subset_1(D_2671, A_2667) | ~m1_subset_1(C_2668, A_2667) | ~m1_subset_1(B_2670, A_2667) | ~m1_subset_1(A_2669, A_2667) | ~m1_subset_1(A_2669, A_2667) | ~m1_subset_1(A_2669, A_2667) | ~m1_subset_1(A_2669, A_2667))), inference(superposition, [status(thm), theory('equality')], [c_12, c_18760])).
% 23.30/13.24  tff(c_20377, plain, (![D_2679, A_2683, B_2680, A_2682, C_2681]: (m1_subset_1(k2_enumset1(A_2682, B_2680, C_2681, D_2679), k1_zfmisc_1(A_2683)) | k1_xboole_0=A_2683 | ~m1_subset_1(D_2679, A_2683) | ~m1_subset_1(C_2681, A_2683) | ~m1_subset_1(B_2680, A_2683) | ~m1_subset_1(A_2682, A_2683) | ~m1_subset_1(A_2682, A_2683) | ~m1_subset_1(A_2682, A_2683) | ~m1_subset_1(A_2682, A_2683) | ~m1_subset_1(A_2682, A_2683))), inference(superposition, [status(thm), theory('equality')], [c_10, c_20153])).
% 23.30/13.24  tff(c_21125, plain, (![A_2765, B_2766, C_2767, A_2768]: (m1_subset_1(k1_enumset1(A_2765, B_2766, C_2767), k1_zfmisc_1(A_2768)) | k1_xboole_0=A_2768 | ~m1_subset_1(C_2767, A_2768) | ~m1_subset_1(B_2766, A_2768) | ~m1_subset_1(A_2765, A_2768) | ~m1_subset_1(A_2765, A_2768) | ~m1_subset_1(A_2765, A_2768) | ~m1_subset_1(A_2765, A_2768) | ~m1_subset_1(A_2765, A_2768) | ~m1_subset_1(A_2765, A_2768))), inference(superposition, [status(thm), theory('equality')], [c_8, c_20377])).
% 23.30/13.24  tff(c_39760, plain, (![A_4066, B_4067, A_4068]: (m1_subset_1(k2_tarski(A_4066, B_4067), k1_zfmisc_1(A_4068)) | k1_xboole_0=A_4068 | ~m1_subset_1(B_4067, A_4068) | ~m1_subset_1(A_4066, A_4068) | ~m1_subset_1(A_4066, A_4068) | ~m1_subset_1(A_4066, A_4068) | ~m1_subset_1(A_4066, A_4068) | ~m1_subset_1(A_4066, A_4068) | ~m1_subset_1(A_4066, A_4068) | ~m1_subset_1(A_4066, A_4068))), inference(superposition, [status(thm), theory('equality')], [c_6, c_21125])).
% 23.30/13.24  tff(c_43137, plain, (![A_4303, A_4304]: (m1_subset_1(k1_tarski(A_4303), k1_zfmisc_1(A_4304)) | k1_xboole_0=A_4304 | ~m1_subset_1(A_4303, A_4304) | ~m1_subset_1(A_4303, A_4304) | ~m1_subset_1(A_4303, A_4304) | ~m1_subset_1(A_4303, A_4304) | ~m1_subset_1(A_4303, A_4304) | ~m1_subset_1(A_4303, A_4304) | ~m1_subset_1(A_4303, A_4304) | ~m1_subset_1(A_4303, A_4304))), inference(superposition, [status(thm), theory('equality')], [c_4, c_39760])).
% 23.30/13.24  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_22, plain, (![A_288]: (r2_hidden('#skF_1'(A_288), A_288) | k1_xboole_0=A_288)), inference(cnfTransformation, [status(thm)], [f_91])).
% 23.30/13.24  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50])).
% 23.30/13.24  tff(c_128, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_77, c_116])).
% 23.30/13.24  tff(c_626, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_128])).
% 23.30/13.24  tff(c_627, plain, (![B_563, A_564]: (m1_subset_1(u1_struct_0(B_563), k1_zfmisc_1(u1_struct_0(A_564))) | ~m1_pre_topc(B_563, A_564) | ~l1_pre_topc(A_564))), inference(cnfTransformation, [status(thm)], [f_115])).
% 23.30/13.24  tff(c_20, plain, (![C_287, B_286, A_285]: (~v1_xboole_0(C_287) | ~m1_subset_1(B_286, k1_zfmisc_1(C_287)) | ~r2_hidden(A_285, B_286))), inference(cnfTransformation, [status(thm)], [f_75])).
% 23.30/13.24  tff(c_645, plain, (![A_583, A_584, B_585]: (~v1_xboole_0(u1_struct_0(A_583)) | ~r2_hidden(A_584, u1_struct_0(B_585)) | ~m1_pre_topc(B_585, A_583) | ~l1_pre_topc(A_583))), inference(resolution, [status(thm)], [c_627, c_20])).
% 23.30/13.24  tff(c_647, plain, (![A_584, B_585]: (~r2_hidden(A_584, u1_struct_0(B_585)) | ~m1_pre_topc(B_585, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_626, c_645])).
% 23.30/13.24  tff(c_651, plain, (![A_586, B_587]: (~r2_hidden(A_586, u1_struct_0(B_587)) | ~m1_pre_topc(B_587, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_647])).
% 23.30/13.24  tff(c_657, plain, (![B_588]: (~m1_pre_topc(B_588, '#skF_3') | u1_struct_0(B_588)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_651])).
% 23.30/13.24  tff(c_661, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_657])).
% 23.30/13.24  tff(c_665, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_661, c_619])).
% 23.30/13.24  tff(c_672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_665])).
% 23.30/13.24  tff(c_673, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_128])).
% 23.30/13.24  tff(c_618, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_127])).
% 23.30/13.24  tff(c_46, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_78, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 23.30/13.24  tff(c_621, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_618, c_78])).
% 23.30/13.24  tff(c_691, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_3', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_673, c_621])).
% 23.30/13.24  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_58, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_54, plain, (v3_borsuk_1('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_72, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 23.30/13.24  tff(c_21417, plain, (![A_2780, C_2781, B_2784, A_2782, B_2783]: (m1_subset_1(k1_enumset1(A_2780, B_2783, C_2781), k1_zfmisc_1(u1_struct_0(A_2782))) | ~m1_pre_topc(B_2784, A_2782) | ~l1_pre_topc(A_2782) | u1_struct_0(B_2784)=k1_xboole_0 | ~m1_subset_1(C_2781, u1_struct_0(B_2784)) | ~m1_subset_1(B_2783, u1_struct_0(B_2784)) | ~m1_subset_1(A_2780, u1_struct_0(B_2784)))), inference(resolution, [status(thm)], [c_21125, c_28])).
% 23.30/13.24  tff(c_21419, plain, (![A_2780, B_2783, C_2781]: (m1_subset_1(k1_enumset1(A_2780, B_2783, C_2781), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1(C_2781, u1_struct_0('#skF_4')) | ~m1_subset_1(B_2783, u1_struct_0('#skF_4')) | ~m1_subset_1(A_2780, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_64, c_21417])).
% 23.30/13.24  tff(c_21422, plain, (![A_2780, B_2783, C_2781]: (m1_subset_1(k1_enumset1(A_2780, B_2783, C_2781), k1_zfmisc_1(u1_struct_0('#skF_3'))) | u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1(C_2781, u1_struct_0('#skF_4')) | ~m1_subset_1(B_2783, u1_struct_0('#skF_4')) | ~m1_subset_1(A_2780, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_21419])).
% 23.30/13.24  tff(c_21424, plain, (![A_2785, B_2786, C_2787]: (m1_subset_1(k1_enumset1(A_2785, B_2786, C_2787), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_2787, u1_struct_0('#skF_4')) | ~m1_subset_1(B_2786, u1_struct_0('#skF_4')) | ~m1_subset_1(A_2785, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_18501, c_21422])).
% 23.30/13.24  tff(c_21600, plain, (![A_2788, B_2789]: (m1_subset_1(k2_tarski(A_2788, B_2789), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_2789, u1_struct_0('#skF_4')) | ~m1_subset_1(A_2788, u1_struct_0('#skF_4')) | ~m1_subset_1(A_2788, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6, c_21424])).
% 23.30/13.24  tff(c_21697, plain, (![A_1]: (m1_subset_1(k1_tarski(A_1), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_21600])).
% 23.30/13.24  tff(c_126, plain, (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_56, c_116])).
% 23.30/13.24  tff(c_620, plain, (v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_126])).
% 23.30/13.24  tff(c_895, plain, (![C_702, A_704, E_706, B_700, G_707, F_701, A_703, D_705, A_699]: (~v1_xboole_0(A_704) | ~r2_hidden(A_699, k5_enumset1(A_703, B_700, C_702, D_705, E_706, F_701, G_707)) | k1_xboole_0=A_704 | ~m1_subset_1(G_707, A_704) | ~m1_subset_1(F_701, A_704) | ~m1_subset_1(E_706, A_704) | ~m1_subset_1(D_705, A_704) | ~m1_subset_1(C_702, A_704) | ~m1_subset_1(B_700, A_704) | ~m1_subset_1(A_703, A_704))), inference(resolution, [status(thm)], [c_871, c_20])).
% 23.30/13.24  tff(c_902, plain, (![F_709, A_708, C_715, E_712, B_711, D_714, A_713, A_710]: (~v1_xboole_0(A_708) | ~r2_hidden(A_710, k4_enumset1(A_713, B_711, C_715, D_714, E_712, F_709)) | k1_xboole_0=A_708 | ~m1_subset_1(F_709, A_708) | ~m1_subset_1(E_712, A_708) | ~m1_subset_1(D_714, A_708) | ~m1_subset_1(C_715, A_708) | ~m1_subset_1(B_711, A_708) | ~m1_subset_1(A_713, A_708) | ~m1_subset_1(A_713, A_708))), inference(superposition, [status(thm), theory('equality')], [c_14, c_895])).
% 23.30/13.24  tff(c_936, plain, (![A_726, C_724, E_729, A_723, B_727, D_728, A_725]: (~v1_xboole_0(A_723) | ~r2_hidden(A_725, k3_enumset1(A_726, B_727, C_724, D_728, E_729)) | k1_xboole_0=A_723 | ~m1_subset_1(E_729, A_723) | ~m1_subset_1(D_728, A_723) | ~m1_subset_1(C_724, A_723) | ~m1_subset_1(B_727, A_723) | ~m1_subset_1(A_726, A_723) | ~m1_subset_1(A_726, A_723) | ~m1_subset_1(A_726, A_723))), inference(superposition, [status(thm), theory('equality')], [c_12, c_902])).
% 23.30/13.24  tff(c_977, plain, (![A_748, D_746, A_751, B_749, C_750, A_747]: (~v1_xboole_0(A_747) | ~r2_hidden(A_748, k2_enumset1(A_751, B_749, C_750, D_746)) | k1_xboole_0=A_747 | ~m1_subset_1(D_746, A_747) | ~m1_subset_1(C_750, A_747) | ~m1_subset_1(B_749, A_747) | ~m1_subset_1(A_751, A_747) | ~m1_subset_1(A_751, A_747) | ~m1_subset_1(A_751, A_747) | ~m1_subset_1(A_751, A_747))), inference(superposition, [status(thm), theory('equality')], [c_10, c_936])).
% 23.30/13.24  tff(c_984, plain, (![C_756, A_753, D_752, A_754, B_755]: (~v1_xboole_0(A_754) | k1_xboole_0=A_754 | ~m1_subset_1(D_752, A_754) | ~m1_subset_1(C_756, A_754) | ~m1_subset_1(B_755, A_754) | ~m1_subset_1(A_753, A_754) | k2_enumset1(A_753, B_755, C_756, D_752)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_977])).
% 23.30/13.24  tff(c_996, plain, (![C_756, B_755, A_753]: (~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))=k1_xboole_0 | ~m1_subset_1(C_756, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(B_755, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(A_753, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k2_enumset1(A_753, B_755, C_756, '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_984])).
% 23.30/13.24  tff(c_1008, plain, (![C_756, B_755, A_753]: (k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))=k1_xboole_0 | ~m1_subset_1(C_756, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(B_755, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(A_753, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k2_enumset1(A_753, B_755, C_756, '#skF_5')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_620, c_996])).
% 23.30/13.24  tff(c_1011, plain, (k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1008])).
% 23.30/13.24  tff(c_1013, plain, (m1_subset_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1011, c_56])).
% 23.30/13.24  tff(c_1201, plain, (![C_811, A_812, B_815, G_807, I_809, E_810, D_806, H_813, F_808, B_814]: (m1_subset_1(k6_enumset1(B_814, C_811, D_806, E_810, F_808, G_807, H_813, I_809), k1_zfmisc_1(u1_struct_0(A_812))) | ~m1_pre_topc(B_815, A_812) | ~l1_pre_topc(A_812) | u1_struct_0(B_815)=k1_xboole_0 | ~m1_subset_1(I_809, u1_struct_0(B_815)) | ~m1_subset_1(H_813, u1_struct_0(B_815)) | ~m1_subset_1(G_807, u1_struct_0(B_815)) | ~m1_subset_1(F_808, u1_struct_0(B_815)) | ~m1_subset_1(E_810, u1_struct_0(B_815)) | ~m1_subset_1(D_806, u1_struct_0(B_815)) | ~m1_subset_1(C_811, u1_struct_0(B_815)) | ~m1_subset_1(B_814, u1_struct_0(B_815)))), inference(resolution, [status(thm)], [c_812, c_28])).
% 23.30/13.24  tff(c_1203, plain, (![C_811, G_807, I_809, E_810, D_806, H_813, F_808, B_814]: (m1_subset_1(k6_enumset1(B_814, C_811, D_806, E_810, F_808, G_807, H_813, I_809), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1(I_809, u1_struct_0('#skF_4')) | ~m1_subset_1(H_813, u1_struct_0('#skF_4')) | ~m1_subset_1(G_807, u1_struct_0('#skF_4')) | ~m1_subset_1(F_808, u1_struct_0('#skF_4')) | ~m1_subset_1(E_810, u1_struct_0('#skF_4')) | ~m1_subset_1(D_806, u1_struct_0('#skF_4')) | ~m1_subset_1(C_811, u1_struct_0('#skF_4')) | ~m1_subset_1(B_814, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_64, c_1201])).
% 23.30/13.24  tff(c_1206, plain, (![C_811, G_807, I_809, E_810, D_806, H_813, F_808, B_814]: (m1_subset_1(k6_enumset1(B_814, C_811, D_806, E_810, F_808, G_807, H_813, I_809), k1_zfmisc_1(u1_struct_0('#skF_3'))) | u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1(I_809, u1_struct_0('#skF_4')) | ~m1_subset_1(H_813, u1_struct_0('#skF_4')) | ~m1_subset_1(G_807, u1_struct_0('#skF_4')) | ~m1_subset_1(F_808, u1_struct_0('#skF_4')) | ~m1_subset_1(E_810, u1_struct_0('#skF_4')) | ~m1_subset_1(D_806, u1_struct_0('#skF_4')) | ~m1_subset_1(C_811, u1_struct_0('#skF_4')) | ~m1_subset_1(B_814, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1203])).
% 23.30/13.24  tff(c_1245, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1206])).
% 23.30/13.24  tff(c_1249, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_619])).
% 23.30/13.24  tff(c_1255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1249])).
% 23.30/13.24  tff(c_1257, plain, (u1_struct_0('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1206])).
% 23.30/13.24  tff(c_1596, plain, (![B_921, F_919, E_922, D_924, A_923, C_925, A_920]: (m1_subset_1(k4_enumset1(A_923, B_921, C_925, D_924, E_922, F_919), k1_zfmisc_1(A_920)) | k1_xboole_0=A_920 | ~m1_subset_1(F_919, A_920) | ~m1_subset_1(E_922, A_920) | ~m1_subset_1(D_924, A_920) | ~m1_subset_1(C_925, A_920) | ~m1_subset_1(B_921, A_920) | ~m1_subset_1(A_923, A_920) | ~m1_subset_1(A_923, A_920) | ~m1_subset_1(A_923, A_920))), inference(superposition, [status(thm), theory('equality')], [c_14, c_871])).
% 23.30/13.24  tff(c_1696, plain, (![B_932, C_930, E_934, A_935, D_933, A_931]: (m1_subset_1(k3_enumset1(A_931, B_932, C_930, D_933, E_934), k1_zfmisc_1(A_935)) | k1_xboole_0=A_935 | ~m1_subset_1(E_934, A_935) | ~m1_subset_1(D_933, A_935) | ~m1_subset_1(C_930, A_935) | ~m1_subset_1(B_932, A_935) | ~m1_subset_1(A_931, A_935) | ~m1_subset_1(A_931, A_935) | ~m1_subset_1(A_931, A_935) | ~m1_subset_1(A_931, A_935))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1596])).
% 23.30/13.24  tff(c_1794, plain, (![C_945, B_944, A_943, D_942, A_946]: (m1_subset_1(k2_enumset1(A_946, B_944, C_945, D_942), k1_zfmisc_1(A_943)) | k1_xboole_0=A_943 | ~m1_subset_1(D_942, A_943) | ~m1_subset_1(C_945, A_943) | ~m1_subset_1(B_944, A_943) | ~m1_subset_1(A_946, A_943) | ~m1_subset_1(A_946, A_943) | ~m1_subset_1(A_946, A_943) | ~m1_subset_1(A_946, A_943) | ~m1_subset_1(A_946, A_943))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1696])).
% 23.30/13.24  tff(c_2019, plain, (![A_991, B_992, C_993, A_994]: (m1_subset_1(k1_enumset1(A_991, B_992, C_993), k1_zfmisc_1(A_994)) | k1_xboole_0=A_994 | ~m1_subset_1(C_993, A_994) | ~m1_subset_1(B_992, A_994) | ~m1_subset_1(A_991, A_994) | ~m1_subset_1(A_991, A_994) | ~m1_subset_1(A_991, A_994) | ~m1_subset_1(A_991, A_994) | ~m1_subset_1(A_991, A_994) | ~m1_subset_1(A_991, A_994))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1794])).
% 23.30/13.24  tff(c_17065, plain, (![A_2194, B_2195, A_2196]: (m1_subset_1(k2_tarski(A_2194, B_2195), k1_zfmisc_1(A_2196)) | k1_xboole_0=A_2196 | ~m1_subset_1(B_2195, A_2196) | ~m1_subset_1(A_2194, A_2196) | ~m1_subset_1(A_2194, A_2196) | ~m1_subset_1(A_2194, A_2196) | ~m1_subset_1(A_2194, A_2196) | ~m1_subset_1(A_2194, A_2196) | ~m1_subset_1(A_2194, A_2196) | ~m1_subset_1(A_2194, A_2196))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2019])).
% 23.30/13.24  tff(c_17647, plain, (![A_2247, A_2248]: (m1_subset_1(k1_tarski(A_2247), k1_zfmisc_1(A_2248)) | k1_xboole_0=A_2248 | ~m1_subset_1(A_2247, A_2248) | ~m1_subset_1(A_2247, A_2248) | ~m1_subset_1(A_2247, A_2248) | ~m1_subset_1(A_2247, A_2248) | ~m1_subset_1(A_2247, A_2248) | ~m1_subset_1(A_2247, A_2248) | ~m1_subset_1(A_2247, A_2248) | ~m1_subset_1(A_2247, A_2248))), inference(superposition, [status(thm), theory('equality')], [c_4, c_17065])).
% 23.30/13.24  tff(c_2130, plain, (![C_1002, A_1000, B_999, A_1001, B_1003]: (m1_subset_1(k1_enumset1(A_1000, B_999, C_1002), k1_zfmisc_1(u1_struct_0(A_1001))) | ~m1_pre_topc(B_1003, A_1001) | ~l1_pre_topc(A_1001) | u1_struct_0(B_1003)=k1_xboole_0 | ~m1_subset_1(C_1002, u1_struct_0(B_1003)) | ~m1_subset_1(B_999, u1_struct_0(B_1003)) | ~m1_subset_1(A_1000, u1_struct_0(B_1003)))), inference(resolution, [status(thm)], [c_2019, c_28])).
% 23.30/13.24  tff(c_2132, plain, (![A_1000, B_999, C_1002]: (m1_subset_1(k1_enumset1(A_1000, B_999, C_1002), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1(C_1002, u1_struct_0('#skF_4')) | ~m1_subset_1(B_999, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1000, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_64, c_2130])).
% 23.30/13.24  tff(c_2135, plain, (![A_1000, B_999, C_1002]: (m1_subset_1(k1_enumset1(A_1000, B_999, C_1002), k1_zfmisc_1(u1_struct_0('#skF_3'))) | u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1(C_1002, u1_struct_0('#skF_4')) | ~m1_subset_1(B_999, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1000, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2132])).
% 23.30/13.24  tff(c_2137, plain, (![A_1004, B_1005, C_1006]: (m1_subset_1(k1_enumset1(A_1004, B_1005, C_1006), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_1006, u1_struct_0('#skF_4')) | ~m1_subset_1(B_1005, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1004, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1257, c_2135])).
% 23.30/13.24  tff(c_2259, plain, (![A_1007, B_1008]: (m1_subset_1(k2_tarski(A_1007, B_1008), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_1008, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1007, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1007, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2137])).
% 23.30/13.24  tff(c_2313, plain, (![A_1]: (m1_subset_1(k1_tarski(A_1), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2259])).
% 23.30/13.24  tff(c_2428, plain, (![A_1021]: (m1_subset_1(k1_tarski(A_1021), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(A_1021, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1021, u1_struct_0('#skF_4')) | ~m1_subset_1(A_1021, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2259])).
% 23.30/13.24  tff(c_2576, plain, (![A_1027, A_1028]: (m1_subset_1(k1_tarski(A_1027), k1_zfmisc_1(u1_struct_0(A_1028))) | ~m1_pre_topc('#skF_3', A_1028) | ~l1_pre_topc(A_1028) | ~m1_subset_1(A_1027, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2428, c_28])).
% 23.30/13.24  tff(c_1050, plain, (![B_757, A_760, A_761, A_759, C_758]: (~v1_xboole_0(A_760) | ~r2_hidden(A_759, k1_enumset1(A_761, B_757, C_758)) | k1_xboole_0=A_760 | ~m1_subset_1(C_758, A_760) | ~m1_subset_1(B_757, A_760) | ~m1_subset_1(A_761, A_760) | ~m1_subset_1(A_761, A_760) | ~m1_subset_1(A_761, A_760) | ~m1_subset_1(A_761, A_760) | ~m1_subset_1(A_761, A_760))), inference(superposition, [status(thm), theory('equality')], [c_8, c_977])).
% 23.30/13.24  tff(c_1140, plain, (![A_787, A_788, A_789, B_790]: (~v1_xboole_0(A_787) | ~r2_hidden(A_788, k2_tarski(A_789, B_790)) | k1_xboole_0=A_787 | ~m1_subset_1(B_790, A_787) | ~m1_subset_1(A_789, A_787) | ~m1_subset_1(A_789, A_787) | ~m1_subset_1(A_789, A_787) | ~m1_subset_1(A_789, A_787) | ~m1_subset_1(A_789, A_787) | ~m1_subset_1(A_789, A_787))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1050])).
% 23.30/13.24  tff(c_1196, plain, (![A_803, A_804, A_805]: (~v1_xboole_0(A_803) | ~r2_hidden(A_804, k1_tarski(A_805)) | k1_xboole_0=A_803 | ~m1_subset_1(A_805, A_803) | ~m1_subset_1(A_805, A_803) | ~m1_subset_1(A_805, A_803) | ~m1_subset_1(A_805, A_803) | ~m1_subset_1(A_805, A_803) | ~m1_subset_1(A_805, A_803) | ~m1_subset_1(A_805, A_803))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1140])).
% 23.30/13.24  tff(c_1200, plain, (![A_803, A_805]: (~v1_xboole_0(A_803) | k1_xboole_0=A_803 | ~m1_subset_1(A_805, A_803) | k1_tarski(A_805)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_1196])).
% 23.30/13.24  tff(c_2641, plain, (![A_1028, A_1027]: (~v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_1028))) | k1_zfmisc_1(u1_struct_0(A_1028))=k1_xboole_0 | k1_tarski(k1_tarski(A_1027))=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_1028) | ~l1_pre_topc(A_1028) | ~m1_subset_1(A_1027, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2576, c_1200])).
% 23.30/13.24  tff(c_15935, plain, (![A_2080]: (k1_tarski(k1_tarski(A_2080))=k1_xboole_0 | ~m1_subset_1(A_2080, u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_2641])).
% 23.30/13.24  tff(c_15939, plain, (k1_tarski(k1_tarski('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_15935])).
% 23.30/13.24  tff(c_30, plain, (![A_313, B_314]: (k6_domain_1(A_313, B_314)=k1_tarski(B_314) | ~m1_subset_1(B_314, A_313) | v1_xboole_0(A_313))), inference(cnfTransformation, [status(thm)], [f_108])).
% 23.30/13.24  tff(c_1898, plain, (![A_962, C_964, B_963, D_961, A_960]: (k6_domain_1(k1_zfmisc_1(A_960), k2_enumset1(A_962, B_963, C_964, D_961))=k1_tarski(k2_enumset1(A_962, B_963, C_964, D_961)) | v1_xboole_0(k1_zfmisc_1(A_960)) | k1_xboole_0=A_960 | ~m1_subset_1(D_961, A_960) | ~m1_subset_1(C_964, A_960) | ~m1_subset_1(B_963, A_960) | ~m1_subset_1(A_962, A_960))), inference(resolution, [status(thm)], [c_1794, c_30])).
% 23.30/13.24  tff(c_1910, plain, (![A_960, A_4, B_5, C_6]: (k6_domain_1(k1_zfmisc_1(A_960), k1_enumset1(A_4, B_5, C_6))=k1_tarski(k2_enumset1(A_4, A_4, B_5, C_6)) | v1_xboole_0(k1_zfmisc_1(A_960)) | k1_xboole_0=A_960 | ~m1_subset_1(C_6, A_960) | ~m1_subset_1(B_5, A_960) | ~m1_subset_1(A_4, A_960) | ~m1_subset_1(A_4, A_960))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1898])).
% 23.30/13.24  tff(c_1916, plain, (![A_965, A_966, B_967, C_968]: (k6_domain_1(k1_zfmisc_1(A_965), k1_enumset1(A_966, B_967, C_968))=k1_tarski(k1_enumset1(A_966, B_967, C_968)) | v1_xboole_0(k1_zfmisc_1(A_965)) | k1_xboole_0=A_965 | ~m1_subset_1(C_968, A_965) | ~m1_subset_1(B_967, A_965) | ~m1_subset_1(A_966, A_965) | ~m1_subset_1(A_966, A_965))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1910])).
% 23.30/13.24  tff(c_1937, plain, (![A_965, A_2, B_3]: (k6_domain_1(k1_zfmisc_1(A_965), k2_tarski(A_2, B_3))=k1_tarski(k1_enumset1(A_2, A_2, B_3)) | v1_xboole_0(k1_zfmisc_1(A_965)) | k1_xboole_0=A_965 | ~m1_subset_1(B_3, A_965) | ~m1_subset_1(A_2, A_965) | ~m1_subset_1(A_2, A_965) | ~m1_subset_1(A_2, A_965))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1916])).
% 23.30/13.24  tff(c_1943, plain, (![A_969, A_970, B_971]: (k6_domain_1(k1_zfmisc_1(A_969), k2_tarski(A_970, B_971))=k1_tarski(k2_tarski(A_970, B_971)) | v1_xboole_0(k1_zfmisc_1(A_969)) | k1_xboole_0=A_969 | ~m1_subset_1(B_971, A_969) | ~m1_subset_1(A_970, A_969) | ~m1_subset_1(A_970, A_969) | ~m1_subset_1(A_970, A_969))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1937])).
% 23.30/13.24  tff(c_1955, plain, (![A_969, A_1]: (k6_domain_1(k1_zfmisc_1(A_969), k1_tarski(A_1))=k1_tarski(k2_tarski(A_1, A_1)) | v1_xboole_0(k1_zfmisc_1(A_969)) | k1_xboole_0=A_969 | ~m1_subset_1(A_1, A_969) | ~m1_subset_1(A_1, A_969) | ~m1_subset_1(A_1, A_969) | ~m1_subset_1(A_1, A_969))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1943])).
% 23.30/13.24  tff(c_1959, plain, (![A_969, A_1]: (k6_domain_1(k1_zfmisc_1(A_969), k1_tarski(A_1))=k1_tarski(k1_tarski(A_1)) | v1_xboole_0(k1_zfmisc_1(A_969)) | k1_xboole_0=A_969 | ~m1_subset_1(A_1, A_969) | ~m1_subset_1(A_1, A_969) | ~m1_subset_1(A_1, A_969) | ~m1_subset_1(A_1, A_969))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1955])).
% 23.30/13.24  tff(c_15960, plain, (![A_969]: (k6_domain_1(k1_zfmisc_1(A_969), k1_xboole_0)=k1_tarski(k1_tarski(k1_tarski('#skF_6'))) | v1_xboole_0(k1_zfmisc_1(A_969)) | k1_xboole_0=A_969 | ~m1_subset_1(k1_tarski('#skF_6'), A_969) | ~m1_subset_1(k1_tarski('#skF_6'), A_969) | ~m1_subset_1(k1_tarski('#skF_6'), A_969) | ~m1_subset_1(k1_tarski('#skF_6'), A_969))), inference(superposition, [status(thm), theory('equality')], [c_15939, c_1959])).
% 23.30/13.24  tff(c_16298, plain, (![A_2132]: (k6_domain_1(k1_zfmisc_1(A_2132), k1_xboole_0)=k1_tarski(k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_2132)) | k1_xboole_0=A_2132 | ~m1_subset_1(k1_tarski('#skF_6'), A_2132) | ~m1_subset_1(k1_tarski('#skF_6'), A_2132) | ~m1_subset_1(k1_tarski('#skF_6'), A_2132) | ~m1_subset_1(k1_tarski('#skF_6'), A_2132))), inference(demodulation, [status(thm), theory('equality')], [c_15939, c_15960])).
% 23.30/13.24  tff(c_16304, plain, (k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))), k1_xboole_0)=k1_tarski(k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | k1_zfmisc_1(u1_struct_0('#skF_3'))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2313, c_16298])).
% 23.30/13.24  tff(c_16310, plain, (k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))), k1_xboole_0)=k1_tarski(k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | k1_zfmisc_1(u1_struct_0('#skF_3'))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16304])).
% 23.30/13.24  tff(c_16311, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_16310])).
% 23.30/13.24  tff(c_16317, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2313, c_16311])).
% 23.30/13.24  tff(c_16324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_16317])).
% 23.30/13.24  tff(c_16326, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_16310])).
% 23.30/13.24  tff(c_44, plain, (![A_331, B_347, C_355, E_361]: (k8_relset_1(u1_struct_0(A_331), u1_struct_0(B_347), C_355, E_361)=k2_pre_topc(A_331, E_361) | ~m1_subset_1(E_361, k1_zfmisc_1(u1_struct_0(A_331))) | ~m1_subset_1(E_361, k1_zfmisc_1(u1_struct_0(B_347))) | ~v3_borsuk_1(C_355, A_331, B_347) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_331), u1_struct_0(B_347)))) | ~v5_pre_topc(C_355, A_331, B_347) | ~v1_funct_2(C_355, u1_struct_0(A_331), u1_struct_0(B_347)) | ~v1_funct_1(C_355) | ~m1_pre_topc(B_347, A_331) | ~v4_tex_2(B_347, A_331) | v2_struct_0(B_347) | ~l1_pre_topc(A_331) | ~v3_tdlat_3(A_331) | ~v2_pre_topc(A_331) | v2_struct_0(A_331))), inference(cnfTransformation, [status(thm)], [f_185])).
% 23.30/13.24  tff(c_16400, plain, (![B_347, C_355]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_347), C_355, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_347))) | ~v3_borsuk_1(C_355, '#skF_3', B_347) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_347)))) | ~v5_pre_topc(C_355, '#skF_3', B_347) | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0(B_347)) | ~v1_funct_1(C_355) | ~m1_pre_topc(B_347, '#skF_3') | ~v4_tex_2(B_347, '#skF_3') | v2_struct_0(B_347) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16326, c_44])).
% 23.30/13.24  tff(c_16470, plain, (![B_347, C_355]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_347), C_355, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_347))) | ~v3_borsuk_1(C_355, '#skF_3', B_347) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_347)))) | ~v5_pre_topc(C_355, '#skF_3', B_347) | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0(B_347)) | ~v1_funct_1(C_355) | ~m1_pre_topc(B_347, '#skF_3') | ~v4_tex_2(B_347, '#skF_3') | v2_struct_0(B_347) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_16400])).
% 23.30/13.24  tff(c_16482, plain, (![B_2136, C_2137]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_2136), C_2137, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_2136))) | ~v3_borsuk_1(C_2137, '#skF_3', B_2136) | ~m1_subset_1(C_2137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_2136)))) | ~v5_pre_topc(C_2137, '#skF_3', B_2136) | ~v1_funct_2(C_2137, u1_struct_0('#skF_3'), u1_struct_0(B_2136)) | ~v1_funct_1(C_2137) | ~m1_pre_topc(B_2136, '#skF_3') | ~v4_tex_2(B_2136, '#skF_3') | v2_struct_0(B_2136))), inference(negUnitSimplification, [status(thm)], [c_76, c_16470])).
% 23.30/13.24  tff(c_16501, plain, (![C_2137]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), C_2137, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_borsuk_1(C_2137, '#skF_3', '#skF_4') | ~m1_subset_1(C_2137, k1_xboole_0) | ~v5_pre_topc(C_2137, '#skF_3', '#skF_4') | ~v1_funct_2(C_2137, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(C_2137) | ~m1_pre_topc('#skF_4', '#skF_3') | ~v4_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1011, c_16482])).
% 23.30/13.24  tff(c_16515, plain, (![C_2137]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), C_2137, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_borsuk_1(C_2137, '#skF_3', '#skF_4') | ~m1_subset_1(C_2137, k1_xboole_0) | ~v5_pre_topc(C_2137, '#skF_3', '#skF_4') | ~v1_funct_2(C_2137, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(C_2137) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_16501])).
% 23.30/13.24  tff(c_16516, plain, (![C_2137]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), C_2137, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_borsuk_1(C_2137, '#skF_3', '#skF_4') | ~m1_subset_1(C_2137, k1_xboole_0) | ~v5_pre_topc(C_2137, '#skF_3', '#skF_4') | ~v1_funct_2(C_2137, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(C_2137))), inference(negUnitSimplification, [status(thm)], [c_68, c_16515])).
% 23.30/13.24  tff(c_16716, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_16516])).
% 23.30/13.24  tff(c_17665, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_17647, c_16716])).
% 23.30/13.24  tff(c_17760, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_17665])).
% 23.30/13.24  tff(c_17762, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1257, c_17760])).
% 23.30/13.24  tff(c_17764, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_16516])).
% 23.30/13.24  tff(c_2471, plain, (![B_347, C_355, A_1021]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_347), C_355, k1_tarski(A_1021))=k2_pre_topc('#skF_3', k1_tarski(A_1021)) | ~m1_subset_1(k1_tarski(A_1021), k1_zfmisc_1(u1_struct_0(B_347))) | ~v3_borsuk_1(C_355, '#skF_3', B_347) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_347)))) | ~v5_pre_topc(C_355, '#skF_3', B_347) | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0(B_347)) | ~v1_funct_1(C_355) | ~m1_pre_topc(B_347, '#skF_3') | ~v4_tex_2(B_347, '#skF_3') | v2_struct_0(B_347) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_subset_1(A_1021, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_2428, c_44])).
% 23.30/13.24  tff(c_2530, plain, (![B_347, C_355, A_1021]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_347), C_355, k1_tarski(A_1021))=k2_pre_topc('#skF_3', k1_tarski(A_1021)) | ~m1_subset_1(k1_tarski(A_1021), k1_zfmisc_1(u1_struct_0(B_347))) | ~v3_borsuk_1(C_355, '#skF_3', B_347) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_347)))) | ~v5_pre_topc(C_355, '#skF_3', B_347) | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0(B_347)) | ~v1_funct_1(C_355) | ~m1_pre_topc(B_347, '#skF_3') | ~v4_tex_2(B_347, '#skF_3') | v2_struct_0(B_347) | v2_struct_0('#skF_3') | ~m1_subset_1(A_1021, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_2471])).
% 23.30/13.24  tff(c_2531, plain, (![B_347, C_355, A_1021]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_347), C_355, k1_tarski(A_1021))=k2_pre_topc('#skF_3', k1_tarski(A_1021)) | ~m1_subset_1(k1_tarski(A_1021), k1_zfmisc_1(u1_struct_0(B_347))) | ~v3_borsuk_1(C_355, '#skF_3', B_347) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_347)))) | ~v5_pre_topc(C_355, '#skF_3', B_347) | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0(B_347)) | ~v1_funct_1(C_355) | ~m1_pre_topc(B_347, '#skF_3') | ~v4_tex_2(B_347, '#skF_3') | v2_struct_0(B_347) | ~m1_subset_1(A_1021, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_76, c_2530])).
% 23.30/13.24  tff(c_17770, plain, (![C_355]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), C_355, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~v3_borsuk_1(C_355, '#skF_3', '#skF_4') | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v5_pre_topc(C_355, '#skF_3', '#skF_4') | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(C_355) | ~m1_pre_topc('#skF_4', '#skF_3') | ~v4_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_17764, c_2531])).
% 23.30/13.24  tff(c_17830, plain, (![C_355]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), C_355, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~v3_borsuk_1(C_355, '#skF_3', '#skF_4') | ~m1_subset_1(C_355, k1_xboole_0) | ~v5_pre_topc(C_355, '#skF_3', '#skF_4') | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(C_355) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_66, c_64, c_1011, c_17770])).
% 23.30/13.24  tff(c_18059, plain, (![C_2257]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), C_2257, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~v3_borsuk_1(C_2257, '#skF_3', '#skF_4') | ~m1_subset_1(C_2257, k1_xboole_0) | ~v5_pre_topc(C_2257, '#skF_3', '#skF_4') | ~v1_funct_2(C_2257, u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1(C_2257))), inference(negUnitSimplification, [status(thm)], [c_68, c_17830])).
% 23.30/13.24  tff(c_18065, plain, (~v3_borsuk_1('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_xboole_0) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18059, c_691])).
% 23.30/13.24  tff(c_18073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1013, c_54, c_18065])).
% 23.30/13.24  tff(c_18075, plain, (k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1008])).
% 23.30/13.24  tff(c_909, plain, (![A_716, F_722, A_717, E_719, C_718, D_721, B_720]: (~v1_xboole_0(A_717) | k1_xboole_0=A_717 | ~m1_subset_1(F_722, A_717) | ~m1_subset_1(E_719, A_717) | ~m1_subset_1(D_721, A_717) | ~m1_subset_1(C_718, A_717) | ~m1_subset_1(B_720, A_717) | ~m1_subset_1(A_716, A_717) | k4_enumset1(A_716, B_720, C_718, D_721, E_719, F_722)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_902])).
% 23.30/13.24  tff(c_921, plain, (![A_716, E_719, C_718, D_721, B_720]: (~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))=k1_xboole_0 | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(D_721, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(C_718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(B_720, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(A_716, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k4_enumset1(A_716, B_720, C_718, D_721, E_719, '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_909])).
% 23.30/13.24  tff(c_933, plain, (![A_716, E_719, C_718, D_721, B_720]: (k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))=k1_xboole_0 | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(D_721, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(C_718, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(B_720, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(A_716, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k4_enumset1(A_716, B_720, C_718, D_721, E_719, '#skF_5')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_620, c_921])).
% 23.30/13.24  tff(c_18543, plain, (![B_2382, A_2381, E_2384, D_2383, C_2385]: (~m1_subset_1(E_2384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(D_2383, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(C_2385, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(B_2382, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(A_2381, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k4_enumset1(A_2381, B_2382, C_2385, D_2383, E_2384, '#skF_5')=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_18075, c_933])).
% 23.30/13.24  tff(c_18694, plain, (![D_2436, C_2437, B_2438, A_2439]: (~m1_subset_1(D_2436, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(C_2437, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(B_2438, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(A_2439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k4_enumset1(A_2439, B_2438, C_2437, D_2436, '#skF_5', '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_18543])).
% 23.30/13.24  tff(c_18706, plain, (![C_2440, B_2441, A_2442]: (~m1_subset_1(C_2440, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(B_2441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(A_2442, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k4_enumset1(A_2442, B_2441, C_2440, '#skF_5', '#skF_5', '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_18694])).
% 23.30/13.24  tff(c_18718, plain, (![B_2443, A_2444]: (~m1_subset_1(B_2443, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~m1_subset_1(A_2444, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k4_enumset1(A_2444, B_2443, '#skF_5', '#skF_5', '#skF_5', '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_18706])).
% 23.30/13.24  tff(c_18730, plain, (![A_2445]: (~m1_subset_1(A_2445, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | k4_enumset1(A_2445, '#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_18718])).
% 23.30/13.24  tff(c_18744, plain, (k4_enumset1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_18730])).
% 23.30/13.24  tff(c_18910, plain, (![A_2458]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2458)) | k1_xboole_0=A_2458 | ~m1_subset_1('#skF_5', A_2458) | ~m1_subset_1('#skF_5', A_2458) | ~m1_subset_1('#skF_5', A_2458) | ~m1_subset_1('#skF_5', A_2458) | ~m1_subset_1('#skF_5', A_2458) | ~m1_subset_1('#skF_5', A_2458) | ~m1_subset_1('#skF_5', A_2458) | ~m1_subset_1('#skF_5', A_2458))), inference(superposition, [status(thm), theory('equality')], [c_18744, c_18760])).
% 23.30/13.24  tff(c_18176, plain, (![A_2277, A_2278, C_2275, B_2274, A_2276]: (~v1_xboole_0(A_2277) | ~r2_hidden(A_2276, k1_enumset1(A_2278, B_2274, C_2275)) | k1_xboole_0=A_2277 | ~m1_subset_1(C_2275, A_2277) | ~m1_subset_1(B_2274, A_2277) | ~m1_subset_1(A_2278, A_2277) | ~m1_subset_1(A_2278, A_2277) | ~m1_subset_1(A_2278, A_2277) | ~m1_subset_1(A_2278, A_2277) | ~m1_subset_1(A_2278, A_2277))), inference(superposition, [status(thm), theory('equality')], [c_8, c_977])).
% 23.30/13.24  tff(c_18297, plain, (![A_2312, A_2313, A_2314, B_2315]: (~v1_xboole_0(A_2312) | ~r2_hidden(A_2313, k2_tarski(A_2314, B_2315)) | k1_xboole_0=A_2312 | ~m1_subset_1(B_2315, A_2312) | ~m1_subset_1(A_2314, A_2312) | ~m1_subset_1(A_2314, A_2312) | ~m1_subset_1(A_2314, A_2312) | ~m1_subset_1(A_2314, A_2312) | ~m1_subset_1(A_2314, A_2312) | ~m1_subset_1(A_2314, A_2312))), inference(superposition, [status(thm), theory('equality')], [c_6, c_18176])).
% 23.30/13.24  tff(c_18427, plain, (![A_2339, A_2340, A_2341]: (~v1_xboole_0(A_2339) | ~r2_hidden(A_2340, k1_tarski(A_2341)) | k1_xboole_0=A_2339 | ~m1_subset_1(A_2341, A_2339) | ~m1_subset_1(A_2341, A_2339) | ~m1_subset_1(A_2341, A_2339) | ~m1_subset_1(A_2341, A_2339) | ~m1_subset_1(A_2341, A_2339) | ~m1_subset_1(A_2341, A_2339) | ~m1_subset_1(A_2341, A_2339))), inference(superposition, [status(thm), theory('equality')], [c_4, c_18297])).
% 23.30/13.24  tff(c_18433, plain, (![A_2339, A_2341]: (~v1_xboole_0(A_2339) | k1_xboole_0=A_2339 | ~m1_subset_1(A_2341, A_2339) | k1_tarski(A_2341)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_18427])).
% 23.30/13.24  tff(c_19030, plain, (![A_2458]: (~v1_xboole_0(k1_zfmisc_1(A_2458)) | k1_zfmisc_1(A_2458)=k1_xboole_0 | k1_tarski(k1_xboole_0)=k1_xboole_0 | k1_xboole_0=A_2458 | ~m1_subset_1('#skF_5', A_2458))), inference(resolution, [status(thm)], [c_18910, c_18433])).
% 23.30/13.24  tff(c_19056, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_19030])).
% 23.30/13.24  tff(c_21806, plain, (![A_2793]: (m1_subset_1(k1_tarski(A_2793), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(A_2793, u1_struct_0('#skF_4')) | ~m1_subset_1(A_2793, u1_struct_0('#skF_4')) | ~m1_subset_1(A_2793, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_21600])).
% 23.30/13.24  tff(c_22030, plain, (![A_2796, A_2797]: (m1_subset_1(k1_tarski(A_2796), k1_zfmisc_1(u1_struct_0(A_2797))) | ~m1_pre_topc('#skF_3', A_2797) | ~l1_pre_topc(A_2797) | ~m1_subset_1(A_2796, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_21806, c_28])).
% 23.30/13.24  tff(c_22153, plain, (![A_2797, A_2796]: (~v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_2797))) | k1_zfmisc_1(u1_struct_0(A_2797))=k1_xboole_0 | k1_tarski(k1_tarski(A_2796))=k1_xboole_0 | ~m1_pre_topc('#skF_3', A_2797) | ~l1_pre_topc(A_2797) | ~m1_subset_1(A_2796, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_22030, c_18433])).
% 23.30/13.24  tff(c_36895, plain, (![A_3837]: (k1_tarski(k1_tarski(A_3837))=k1_xboole_0 | ~m1_subset_1(A_3837, u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_22153])).
% 23.30/13.24  tff(c_36899, plain, (k1_tarski(k1_tarski('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_36895])).
% 23.30/13.24  tff(c_20602, plain, (![B_2691, C_2689, D_2690, A_2693, A_2692]: (k6_domain_1(k1_zfmisc_1(A_2693), k2_enumset1(A_2692, B_2691, C_2689, D_2690))=k1_tarski(k2_enumset1(A_2692, B_2691, C_2689, D_2690)) | v1_xboole_0(k1_zfmisc_1(A_2693)) | k1_xboole_0=A_2693 | ~m1_subset_1(D_2690, A_2693) | ~m1_subset_1(C_2689, A_2693) | ~m1_subset_1(B_2691, A_2693) | ~m1_subset_1(A_2692, A_2693))), inference(resolution, [status(thm)], [c_20377, c_30])).
% 23.30/13.24  tff(c_20614, plain, (![A_2693, A_4, B_5, C_6]: (k6_domain_1(k1_zfmisc_1(A_2693), k1_enumset1(A_4, B_5, C_6))=k1_tarski(k2_enumset1(A_4, A_4, B_5, C_6)) | v1_xboole_0(k1_zfmisc_1(A_2693)) | k1_xboole_0=A_2693 | ~m1_subset_1(C_6, A_2693) | ~m1_subset_1(B_5, A_2693) | ~m1_subset_1(A_4, A_2693) | ~m1_subset_1(A_4, A_2693))), inference(superposition, [status(thm), theory('equality')], [c_8, c_20602])).
% 23.30/13.24  tff(c_20620, plain, (![A_2694, A_2695, B_2696, C_2697]: (k6_domain_1(k1_zfmisc_1(A_2694), k1_enumset1(A_2695, B_2696, C_2697))=k1_tarski(k1_enumset1(A_2695, B_2696, C_2697)) | v1_xboole_0(k1_zfmisc_1(A_2694)) | k1_xboole_0=A_2694 | ~m1_subset_1(C_2697, A_2694) | ~m1_subset_1(B_2696, A_2694) | ~m1_subset_1(A_2695, A_2694) | ~m1_subset_1(A_2695, A_2694))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_20614])).
% 23.30/13.24  tff(c_20641, plain, (![A_2694, A_2, B_3]: (k6_domain_1(k1_zfmisc_1(A_2694), k2_tarski(A_2, B_3))=k1_tarski(k1_enumset1(A_2, A_2, B_3)) | v1_xboole_0(k1_zfmisc_1(A_2694)) | k1_xboole_0=A_2694 | ~m1_subset_1(B_3, A_2694) | ~m1_subset_1(A_2, A_2694) | ~m1_subset_1(A_2, A_2694) | ~m1_subset_1(A_2, A_2694))), inference(superposition, [status(thm), theory('equality')], [c_6, c_20620])).
% 23.30/13.24  tff(c_20647, plain, (![A_2698, A_2699, B_2700]: (k6_domain_1(k1_zfmisc_1(A_2698), k2_tarski(A_2699, B_2700))=k1_tarski(k2_tarski(A_2699, B_2700)) | v1_xboole_0(k1_zfmisc_1(A_2698)) | k1_xboole_0=A_2698 | ~m1_subset_1(B_2700, A_2698) | ~m1_subset_1(A_2699, A_2698) | ~m1_subset_1(A_2699, A_2698) | ~m1_subset_1(A_2699, A_2698))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20641])).
% 23.30/13.24  tff(c_20665, plain, (![A_2698, A_1]: (k6_domain_1(k1_zfmisc_1(A_2698), k1_tarski(A_1))=k1_tarski(k2_tarski(A_1, A_1)) | v1_xboole_0(k1_zfmisc_1(A_2698)) | k1_xboole_0=A_2698 | ~m1_subset_1(A_1, A_2698) | ~m1_subset_1(A_1, A_2698) | ~m1_subset_1(A_1, A_2698) | ~m1_subset_1(A_1, A_2698))), inference(superposition, [status(thm), theory('equality')], [c_4, c_20647])).
% 23.30/13.24  tff(c_20669, plain, (![A_2698, A_1]: (k6_domain_1(k1_zfmisc_1(A_2698), k1_tarski(A_1))=k1_tarski(k1_tarski(A_1)) | v1_xboole_0(k1_zfmisc_1(A_2698)) | k1_xboole_0=A_2698 | ~m1_subset_1(A_1, A_2698) | ~m1_subset_1(A_1, A_2698) | ~m1_subset_1(A_1, A_2698) | ~m1_subset_1(A_1, A_2698))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_20665])).
% 23.30/13.24  tff(c_36918, plain, (![A_2698]: (k6_domain_1(k1_zfmisc_1(A_2698), k1_xboole_0)=k1_tarski(k1_tarski(k1_tarski('#skF_6'))) | v1_xboole_0(k1_zfmisc_1(A_2698)) | k1_xboole_0=A_2698 | ~m1_subset_1(k1_tarski('#skF_6'), A_2698) | ~m1_subset_1(k1_tarski('#skF_6'), A_2698) | ~m1_subset_1(k1_tarski('#skF_6'), A_2698) | ~m1_subset_1(k1_tarski('#skF_6'), A_2698))), inference(superposition, [status(thm), theory('equality')], [c_36899, c_20669])).
% 23.30/13.24  tff(c_37410, plain, (![A_3884]: (k6_domain_1(k1_zfmisc_1(A_3884), k1_xboole_0)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_3884)) | k1_xboole_0=A_3884 | ~m1_subset_1(k1_tarski('#skF_6'), A_3884) | ~m1_subset_1(k1_tarski('#skF_6'), A_3884) | ~m1_subset_1(k1_tarski('#skF_6'), A_3884) | ~m1_subset_1(k1_tarski('#skF_6'), A_3884))), inference(demodulation, [status(thm), theory('equality')], [c_19056, c_36899, c_36918])).
% 23.30/13.24  tff(c_37416, plain, (k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))), k1_xboole_0)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | k1_zfmisc_1(u1_struct_0('#skF_3'))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_21697, c_37410])).
% 23.30/13.24  tff(c_37422, plain, (k6_domain_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))), k1_xboole_0)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | k1_zfmisc_1(u1_struct_0('#skF_3'))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_37416])).
% 23.30/13.24  tff(c_37444, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_37422])).
% 23.30/13.24  tff(c_37450, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_21697, c_37444])).
% 23.30/13.24  tff(c_37457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_37450])).
% 23.30/13.24  tff(c_37459, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_37422])).
% 23.30/13.24  tff(c_37538, plain, (![B_347, C_355]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_347), C_355, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_347))) | ~v3_borsuk_1(C_355, '#skF_3', B_347) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_347)))) | ~v5_pre_topc(C_355, '#skF_3', B_347) | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0(B_347)) | ~v1_funct_1(C_355) | ~m1_pre_topc(B_347, '#skF_3') | ~v4_tex_2(B_347, '#skF_3') | v2_struct_0(B_347) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_37459, c_44])).
% 23.30/13.24  tff(c_37621, plain, (![B_347, C_355]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_347), C_355, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_347))) | ~v3_borsuk_1(C_355, '#skF_3', B_347) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_347)))) | ~v5_pre_topc(C_355, '#skF_3', B_347) | ~v1_funct_2(C_355, u1_struct_0('#skF_3'), u1_struct_0(B_347)) | ~v1_funct_1(C_355) | ~m1_pre_topc(B_347, '#skF_3') | ~v4_tex_2(B_347, '#skF_3') | v2_struct_0(B_347) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_37538])).
% 23.30/13.24  tff(c_37814, plain, (![B_3897, C_3898]: (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0(B_3897), C_3898, k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_3897))) | ~v3_borsuk_1(C_3898, '#skF_3', B_3897) | ~m1_subset_1(C_3898, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_3897)))) | ~v5_pre_topc(C_3898, '#skF_3', B_3897) | ~v1_funct_2(C_3898, u1_struct_0('#skF_3'), u1_struct_0(B_3897)) | ~v1_funct_1(C_3898) | ~m1_pre_topc(B_3897, '#skF_3') | ~v4_tex_2(B_3897, '#skF_3') | v2_struct_0(B_3897))), inference(negUnitSimplification, [status(thm)], [c_76, c_37621])).
% 23.30/13.24  tff(c_37845, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_borsuk_1('#skF_5', '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~v4_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_37814])).
% 23.30/13.24  tff(c_37855, plain, (k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', k1_tarski('#skF_6'))=k2_pre_topc('#skF_3', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_58, c_54, c_37845])).
% 23.30/13.24  tff(c_37856, plain, (~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_691, c_37855])).
% 23.30/13.24  tff(c_43251, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_43137, c_37856])).
% 23.30/13.24  tff(c_43510, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_43251])).
% 23.30/13.24  tff(c_43512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18501, c_43510])).
% 23.30/13.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.30/13.24  
% 23.30/13.24  Inference rules
% 23.30/13.24  ----------------------
% 23.30/13.24  #Ref     : 0
% 23.30/13.24  #Sup     : 10879
% 23.30/13.24  #Fact    : 0
% 23.30/13.24  #Define  : 0
% 23.30/13.24  #Split   : 125
% 23.30/13.24  #Chain   : 0
% 23.30/13.24  #Close   : 0
% 23.30/13.24  
% 23.30/13.24  Ordering : KBO
% 23.30/13.24  
% 23.30/13.24  Simplification rules
% 23.30/13.24  ----------------------
% 23.30/13.24  #Subsume      : 3384
% 23.30/13.24  #Demod        : 4732
% 23.30/13.24  #Tautology    : 1374
% 23.30/13.24  #SimpNegUnit  : 1847
% 23.30/13.24  #BackRed      : 379
% 23.30/13.24  
% 23.30/13.24  #Partial instantiations: 0
% 23.30/13.24  #Strategies tried      : 1
% 23.30/13.24  
% 23.30/13.24  Timing (in seconds)
% 23.30/13.24  ----------------------
% 23.30/13.24  Preprocessing        : 0.40
% 23.30/13.24  Parsing              : 0.20
% 23.30/13.24  CNF conversion       : 0.05
% 23.30/13.25  Main loop            : 12.02
% 23.30/13.25  Inferencing          : 2.04
% 23.30/13.25  Reduction            : 3.37
% 23.30/13.25  Demodulation         : 2.45
% 23.30/13.25  BG Simplification    : 0.25
% 23.30/13.25  Subsumption          : 5.72
% 23.30/13.25  Abstraction          : 0.47
% 23.30/13.25  MUC search           : 0.00
% 23.30/13.25  Cooper               : 0.00
% 23.30/13.25  Total                : 12.50
% 23.30/13.25  Index Insertion      : 0.00
% 23.30/13.25  Index Deletion       : 0.00
% 23.30/13.25  Index Matching       : 0.00
% 23.30/13.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
