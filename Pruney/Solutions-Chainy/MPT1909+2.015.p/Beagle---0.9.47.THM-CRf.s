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
% DateTime   : Thu Dec  3 10:30:39 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 300 expanded)
%              Number of leaves         :   54 ( 127 expanded)
%              Depth                    :   21
%              Number of atoms          :  452 (1556 expanded)
%              Number of equality atoms :   58 ( 210 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_116,axiom,(
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

tff(f_131,axiom,(
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

tff(f_169,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_42,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_71,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_563,plain,(
    ! [B_552,C_551,F_557,E_555,I_556,G_549,H_554,A_553,D_550] :
      ( m1_subset_1(k6_enumset1(B_552,C_551,D_550,E_555,F_557,G_549,H_554,I_556),k1_zfmisc_1(A_553))
      | k1_xboole_0 = A_553
      | ~ m1_subset_1(I_556,A_553)
      | ~ m1_subset_1(H_554,A_553)
      | ~ m1_subset_1(G_549,A_553)
      | ~ m1_subset_1(F_557,A_553)
      | ~ m1_subset_1(E_555,A_553)
      | ~ m1_subset_1(D_550,A_553)
      | ~ m1_subset_1(C_551,A_553)
      | ~ m1_subset_1(B_552,A_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [C_294,A_288,B_292] :
      ( m1_subset_1(C_294,k1_zfmisc_1(u1_struct_0(A_288)))
      | ~ m1_subset_1(C_294,k1_zfmisc_1(u1_struct_0(B_292)))
      | ~ m1_pre_topc(B_292,A_288)
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5093,plain,(
    ! [I_1158,F_1163,A_1164,B_1159,G_1161,D_1162,H_1156,C_1157,B_1155,E_1160] :
      ( m1_subset_1(k6_enumset1(B_1155,C_1157,D_1162,E_1160,F_1163,G_1161,H_1156,I_1158),k1_zfmisc_1(u1_struct_0(A_1164)))
      | ~ m1_pre_topc(B_1159,A_1164)
      | ~ l1_pre_topc(A_1164)
      | u1_struct_0(B_1159) = k1_xboole_0
      | ~ m1_subset_1(I_1158,u1_struct_0(B_1159))
      | ~ m1_subset_1(H_1156,u1_struct_0(B_1159))
      | ~ m1_subset_1(G_1161,u1_struct_0(B_1159))
      | ~ m1_subset_1(F_1163,u1_struct_0(B_1159))
      | ~ m1_subset_1(E_1160,u1_struct_0(B_1159))
      | ~ m1_subset_1(D_1162,u1_struct_0(B_1159))
      | ~ m1_subset_1(C_1157,u1_struct_0(B_1159))
      | ~ m1_subset_1(B_1155,u1_struct_0(B_1159)) ) ),
    inference(resolution,[status(thm)],[c_563,c_22])).

tff(c_5095,plain,(
    ! [I_1158,F_1163,G_1161,D_1162,H_1156,C_1157,B_1155,E_1160] :
      ( m1_subset_1(k6_enumset1(B_1155,C_1157,D_1162,E_1160,F_1163,G_1161,H_1156,I_1158),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(I_1158,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_1156,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_1161,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1163,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_1160,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_1162,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_1157,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1155,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_58,c_5093])).

tff(c_5098,plain,(
    ! [I_1158,F_1163,G_1161,D_1162,H_1156,C_1157,B_1155,E_1160] :
      ( m1_subset_1(k6_enumset1(B_1155,C_1157,D_1162,E_1160,F_1163,G_1161,H_1156,I_1158),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(I_1158,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(H_1156,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_1161,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1163,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_1160,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_1162,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_1157,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1155,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5095])).

tff(c_5208,plain,(
    u1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5098])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_60,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_110,plain,(
    ! [A_378,B_379] :
      ( k6_domain_1(A_378,B_379) = k1_tarski(B_379)
      | ~ m1_subset_1(B_379,A_378)
      | v1_xboole_0(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_122,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71,c_110])).

tff(c_323,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_26,plain,(
    ! [B_299,A_297] :
      ( m1_subset_1(u1_struct_0(B_299),k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ m1_pre_topc(B_299,A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_424,plain,(
    ! [B_490,A_491] :
      ( v3_tex_2(u1_struct_0(B_490),A_491)
      | ~ m1_subset_1(u1_struct_0(B_490),k1_zfmisc_1(u1_struct_0(A_491)))
      | ~ v4_tex_2(B_490,A_491)
      | ~ m1_pre_topc(B_490,A_491)
      | ~ l1_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_429,plain,(
    ! [B_492,A_493] :
      ( v3_tex_2(u1_struct_0(B_492),A_493)
      | ~ v4_tex_2(B_492,A_493)
      | v2_struct_0(A_493)
      | ~ m1_pre_topc(B_492,A_493)
      | ~ l1_pre_topc(A_493) ) ),
    inference(resolution,[status(thm)],[c_26,c_424])).

tff(c_372,plain,(
    ! [B_470,A_471] :
      ( ~ v3_tex_2(B_470,A_471)
      | ~ m1_subset_1(B_470,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ v1_xboole_0(B_470)
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | v2_struct_0(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_376,plain,(
    ! [B_299,A_297] :
      ( ~ v3_tex_2(u1_struct_0(B_299),A_297)
      | ~ v1_xboole_0(u1_struct_0(B_299))
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297)
      | ~ m1_pre_topc(B_299,A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(resolution,[status(thm)],[c_26,c_372])).

tff(c_434,plain,(
    ! [B_494,A_495] :
      ( ~ v1_xboole_0(u1_struct_0(B_494))
      | ~ v2_pre_topc(A_495)
      | ~ v4_tex_2(B_494,A_495)
      | v2_struct_0(A_495)
      | ~ m1_pre_topc(B_494,A_495)
      | ~ l1_pre_topc(A_495) ) ),
    inference(resolution,[status(thm)],[c_429,c_376])).

tff(c_438,plain,(
    ! [A_496] :
      ( ~ v2_pre_topc(A_496)
      | ~ v4_tex_2('#skF_3',A_496)
      | v2_struct_0(A_496)
      | ~ m1_pre_topc('#skF_3',A_496)
      | ~ l1_pre_topc(A_496) ) ),
    inference(resolution,[status(thm)],[c_323,c_434])).

tff(c_445,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_438])).

tff(c_449,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_68,c_445])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_449])).

tff(c_453,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_5217,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5208,c_453])).

tff(c_5224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5217])).

tff(c_5226,plain,(
    u1_struct_0('#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5098])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_52,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_48,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

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

tff(c_649,plain,(
    ! [B_587,D_586,E_582,G_585,F_584,A_580,C_581,A_583] :
      ( m1_subset_1(k5_enumset1(A_580,B_587,C_581,D_586,E_582,F_584,G_585),k1_zfmisc_1(A_583))
      | k1_xboole_0 = A_583
      | ~ m1_subset_1(G_585,A_583)
      | ~ m1_subset_1(F_584,A_583)
      | ~ m1_subset_1(E_582,A_583)
      | ~ m1_subset_1(D_586,A_583)
      | ~ m1_subset_1(C_581,A_583)
      | ~ m1_subset_1(B_587,A_583)
      | ~ m1_subset_1(A_580,A_583)
      | ~ m1_subset_1(A_580,A_583) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_563])).

tff(c_728,plain,(
    ! [B_606,C_611,A_610,F_605,E_607,D_609,A_608] :
      ( m1_subset_1(k4_enumset1(A_608,B_606,C_611,D_609,E_607,F_605),k1_zfmisc_1(A_610))
      | k1_xboole_0 = A_610
      | ~ m1_subset_1(F_605,A_610)
      | ~ m1_subset_1(E_607,A_610)
      | ~ m1_subset_1(D_609,A_610)
      | ~ m1_subset_1(C_611,A_610)
      | ~ m1_subset_1(B_606,A_610)
      | ~ m1_subset_1(A_608,A_610)
      | ~ m1_subset_1(A_608,A_610)
      | ~ m1_subset_1(A_608,A_610) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_649])).

tff(c_789,plain,(
    ! [D_623,A_621,B_622,E_624,C_620,A_619] :
      ( m1_subset_1(k3_enumset1(A_621,B_622,C_620,D_623,E_624),k1_zfmisc_1(A_619))
      | k1_xboole_0 = A_619
      | ~ m1_subset_1(E_624,A_619)
      | ~ m1_subset_1(D_623,A_619)
      | ~ m1_subset_1(C_620,A_619)
      | ~ m1_subset_1(B_622,A_619)
      | ~ m1_subset_1(A_621,A_619)
      | ~ m1_subset_1(A_621,A_619)
      | ~ m1_subset_1(A_621,A_619)
      | ~ m1_subset_1(A_621,A_619) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_728])).

tff(c_4871,plain,(
    ! [D_1118,A_1121,C_1120,A_1122,B_1119] :
      ( m1_subset_1(k2_enumset1(A_1122,B_1119,C_1120,D_1118),k1_zfmisc_1(A_1121))
      | k1_xboole_0 = A_1121
      | ~ m1_subset_1(D_1118,A_1121)
      | ~ m1_subset_1(C_1120,A_1121)
      | ~ m1_subset_1(B_1119,A_1121)
      | ~ m1_subset_1(A_1122,A_1121)
      | ~ m1_subset_1(A_1122,A_1121)
      | ~ m1_subset_1(A_1122,A_1121)
      | ~ m1_subset_1(A_1122,A_1121)
      | ~ m1_subset_1(A_1122,A_1121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_789])).

tff(c_5109,plain,(
    ! [A_1167,B_1168,C_1169,A_1170] :
      ( m1_subset_1(k1_enumset1(A_1167,B_1168,C_1169),k1_zfmisc_1(A_1170))
      | k1_xboole_0 = A_1170
      | ~ m1_subset_1(C_1169,A_1170)
      | ~ m1_subset_1(B_1168,A_1170)
      | ~ m1_subset_1(A_1167,A_1170)
      | ~ m1_subset_1(A_1167,A_1170)
      | ~ m1_subset_1(A_1167,A_1170)
      | ~ m1_subset_1(A_1167,A_1170)
      | ~ m1_subset_1(A_1167,A_1170)
      | ~ m1_subset_1(A_1167,A_1170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4871])).

tff(c_6920,plain,(
    ! [A_1372,B_1373,A_1374] :
      ( m1_subset_1(k2_tarski(A_1372,B_1373),k1_zfmisc_1(A_1374))
      | k1_xboole_0 = A_1374
      | ~ m1_subset_1(B_1373,A_1374)
      | ~ m1_subset_1(A_1372,A_1374)
      | ~ m1_subset_1(A_1372,A_1374)
      | ~ m1_subset_1(A_1372,A_1374)
      | ~ m1_subset_1(A_1372,A_1374)
      | ~ m1_subset_1(A_1372,A_1374)
      | ~ m1_subset_1(A_1372,A_1374)
      | ~ m1_subset_1(A_1372,A_1374) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5109])).

tff(c_7895,plain,(
    ! [A_1490,A_1491] :
      ( m1_subset_1(k1_tarski(A_1490),k1_zfmisc_1(A_1491))
      | k1_xboole_0 = A_1491
      | ~ m1_subset_1(A_1490,A_1491)
      | ~ m1_subset_1(A_1490,A_1491)
      | ~ m1_subset_1(A_1490,A_1491)
      | ~ m1_subset_1(A_1490,A_1491)
      | ~ m1_subset_1(A_1490,A_1491)
      | ~ m1_subset_1(A_1490,A_1491)
      | ~ m1_subset_1(A_1490,A_1491)
      | ~ m1_subset_1(A_1490,A_1491) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_6920])).

tff(c_66,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_5315,plain,(
    ! [C_1178,B_1180,A_1182,B_1179,A_1181] :
      ( m1_subset_1(k1_enumset1(A_1182,B_1180,C_1178),k1_zfmisc_1(u1_struct_0(A_1181)))
      | ~ m1_pre_topc(B_1179,A_1181)
      | ~ l1_pre_topc(A_1181)
      | u1_struct_0(B_1179) = k1_xboole_0
      | ~ m1_subset_1(C_1178,u1_struct_0(B_1179))
      | ~ m1_subset_1(B_1180,u1_struct_0(B_1179))
      | ~ m1_subset_1(A_1182,u1_struct_0(B_1179)) ) ),
    inference(resolution,[status(thm)],[c_5109,c_22])).

tff(c_5317,plain,(
    ! [A_1182,B_1180,C_1178] :
      ( m1_subset_1(k1_enumset1(A_1182,B_1180,C_1178),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_1178,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1180,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1182,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_58,c_5315])).

tff(c_5320,plain,(
    ! [A_1182,B_1180,C_1178] :
      ( m1_subset_1(k1_enumset1(A_1182,B_1180,C_1178),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(C_1178,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1180,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1182,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5317])).

tff(c_5326,plain,(
    ! [A_1187,B_1188,C_1189] :
      ( m1_subset_1(k1_enumset1(A_1187,B_1188,C_1189),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(C_1189,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_1188,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1187,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5226,c_5320])).

tff(c_5372,plain,(
    ! [A_1190,B_1191] :
      ( m1_subset_1(k2_tarski(A_1190,B_1191),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_1191,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1190,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1190,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5326])).

tff(c_5429,plain,(
    ! [A_1198] :
      ( m1_subset_1(k1_tarski(A_1198),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(A_1198,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1198,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1198,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5372])).

tff(c_38,plain,(
    ! [A_313,B_329,C_337,E_343] :
      ( k8_relset_1(u1_struct_0(A_313),u1_struct_0(B_329),C_337,E_343) = k2_pre_topc(A_313,E_343)
      | ~ m1_subset_1(E_343,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ m1_subset_1(E_343,k1_zfmisc_1(u1_struct_0(B_329)))
      | ~ v3_borsuk_1(C_337,A_313,B_329)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_313),u1_struct_0(B_329))))
      | ~ v5_pre_topc(C_337,A_313,B_329)
      | ~ v1_funct_2(C_337,u1_struct_0(A_313),u1_struct_0(B_329))
      | ~ v1_funct_1(C_337)
      | ~ m1_pre_topc(B_329,A_313)
      | ~ v4_tex_2(B_329,A_313)
      | v2_struct_0(B_329)
      | ~ l1_pre_topc(A_313)
      | ~ v3_tdlat_3(A_313)
      | ~ v2_pre_topc(A_313)
      | v2_struct_0(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_5443,plain,(
    ! [B_329,C_337,A_1198] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_329),C_337,k1_tarski(A_1198)) = k2_pre_topc('#skF_2',k1_tarski(A_1198))
      | ~ m1_subset_1(k1_tarski(A_1198),k1_zfmisc_1(u1_struct_0(B_329)))
      | ~ v3_borsuk_1(C_337,'#skF_2',B_329)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_329))))
      | ~ v5_pre_topc(C_337,'#skF_2',B_329)
      | ~ v1_funct_2(C_337,u1_struct_0('#skF_2'),u1_struct_0(B_329))
      | ~ v1_funct_1(C_337)
      | ~ m1_pre_topc(B_329,'#skF_2')
      | ~ v4_tex_2(B_329,'#skF_2')
      | v2_struct_0(B_329)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_1198,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5429,c_38])).

tff(c_5463,plain,(
    ! [B_329,C_337,A_1198] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_329),C_337,k1_tarski(A_1198)) = k2_pre_topc('#skF_2',k1_tarski(A_1198))
      | ~ m1_subset_1(k1_tarski(A_1198),k1_zfmisc_1(u1_struct_0(B_329)))
      | ~ v3_borsuk_1(C_337,'#skF_2',B_329)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_329))))
      | ~ v5_pre_topc(C_337,'#skF_2',B_329)
      | ~ v1_funct_2(C_337,u1_struct_0('#skF_2'),u1_struct_0(B_329))
      | ~ v1_funct_1(C_337)
      | ~ m1_pre_topc(B_329,'#skF_2')
      | ~ v4_tex_2(B_329,'#skF_2')
      | v2_struct_0(B_329)
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(A_1198,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_5443])).

tff(c_5464,plain,(
    ! [B_329,C_337,A_1198] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_329),C_337,k1_tarski(A_1198)) = k2_pre_topc('#skF_2',k1_tarski(A_1198))
      | ~ m1_subset_1(k1_tarski(A_1198),k1_zfmisc_1(u1_struct_0(B_329)))
      | ~ v3_borsuk_1(C_337,'#skF_2',B_329)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_329))))
      | ~ v5_pre_topc(C_337,'#skF_2',B_329)
      | ~ v1_funct_2(C_337,u1_struct_0('#skF_2'),u1_struct_0(B_329))
      | ~ v1_funct_1(C_337)
      | ~ m1_pre_topc(B_329,'#skF_2')
      | ~ v4_tex_2(B_329,'#skF_2')
      | v2_struct_0(B_329)
      | ~ m1_subset_1(A_1198,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_5463])).

tff(c_11272,plain,(
    ! [B_2027,C_2028,A_2029] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_2027),C_2028,k1_tarski(A_2029)) = k2_pre_topc('#skF_2',k1_tarski(A_2029))
      | ~ v3_borsuk_1(C_2028,'#skF_2',B_2027)
      | ~ m1_subset_1(C_2028,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_2027))))
      | ~ v5_pre_topc(C_2028,'#skF_2',B_2027)
      | ~ v1_funct_2(C_2028,u1_struct_0('#skF_2'),u1_struct_0(B_2027))
      | ~ v1_funct_1(C_2028)
      | ~ m1_pre_topc(B_2027,'#skF_2')
      | ~ v4_tex_2(B_2027,'#skF_2')
      | v2_struct_0(B_2027)
      | ~ m1_subset_1(A_2029,u1_struct_0('#skF_3'))
      | u1_struct_0(B_2027) = k1_xboole_0
      | ~ m1_subset_1(A_2029,u1_struct_0(B_2027)) ) ),
    inference(resolution,[status(thm)],[c_7895,c_5464])).

tff(c_11298,plain,(
    ! [A_2029] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_2029)) = k2_pre_topc('#skF_2',k1_tarski(A_2029))
      | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ v4_tex_2('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(A_2029,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_50,c_11272])).

tff(c_11309,plain,(
    ! [A_2029] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_2029)) = k2_pre_topc('#skF_2',k1_tarski(A_2029))
      | v2_struct_0('#skF_3')
      | u1_struct_0('#skF_3') = k1_xboole_0
      | ~ m1_subset_1(A_2029,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_48,c_11298])).

tff(c_11311,plain,(
    ! [A_2030] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski(A_2030)) = k2_pre_topc('#skF_2',k1_tarski(A_2030))
      | ~ m1_subset_1(A_2030,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5226,c_62,c_11309])).

tff(c_452,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_121,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_110])).

tff(c_123,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_286,plain,(
    ! [B_439,A_440] :
      ( m1_subset_1(u1_struct_0(B_439),k1_zfmisc_1(u1_struct_0(A_440)))
      | ~ m1_pre_topc(B_439,A_440)
      | ~ l1_pre_topc(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [B_287,A_285] :
      ( v1_xboole_0(B_287)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(A_285))
      | ~ v1_xboole_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_299,plain,(
    ! [B_441,A_442] :
      ( v1_xboole_0(u1_struct_0(B_441))
      | ~ v1_xboole_0(u1_struct_0(A_442))
      | ~ m1_pre_topc(B_441,A_442)
      | ~ l1_pre_topc(A_442) ) ),
    inference(resolution,[status(thm)],[c_286,c_20])).

tff(c_301,plain,(
    ! [B_441] :
      ( v1_xboole_0(u1_struct_0(B_441))
      | ~ m1_pre_topc(B_441,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_123,c_299])).

tff(c_306,plain,(
    ! [B_443] :
      ( v1_xboole_0(u1_struct_0(B_443))
      | ~ m1_pre_topc(B_443,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_301])).

tff(c_133,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_250,plain,(
    ! [B_432,A_433] :
      ( v3_tex_2(u1_struct_0(B_432),A_433)
      | ~ m1_subset_1(u1_struct_0(B_432),k1_zfmisc_1(u1_struct_0(A_433)))
      | ~ v4_tex_2(B_432,A_433)
      | ~ m1_pre_topc(B_432,A_433)
      | ~ l1_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_255,plain,(
    ! [B_434,A_435] :
      ( v3_tex_2(u1_struct_0(B_434),A_435)
      | ~ v4_tex_2(B_434,A_435)
      | v2_struct_0(A_435)
      | ~ m1_pre_topc(B_434,A_435)
      | ~ l1_pre_topc(A_435) ) ),
    inference(resolution,[status(thm)],[c_26,c_250])).

tff(c_188,plain,(
    ! [B_409,A_410] :
      ( ~ v3_tex_2(B_409,A_410)
      | ~ m1_subset_1(B_409,k1_zfmisc_1(u1_struct_0(A_410)))
      | ~ v1_xboole_0(B_409)
      | ~ l1_pre_topc(A_410)
      | ~ v2_pre_topc(A_410)
      | v2_struct_0(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_192,plain,(
    ! [B_299,A_297] :
      ( ~ v3_tex_2(u1_struct_0(B_299),A_297)
      | ~ v1_xboole_0(u1_struct_0(B_299))
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297)
      | ~ m1_pre_topc(B_299,A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_260,plain,(
    ! [B_436,A_437] :
      ( ~ v1_xboole_0(u1_struct_0(B_436))
      | ~ v2_pre_topc(A_437)
      | ~ v4_tex_2(B_436,A_437)
      | v2_struct_0(A_437)
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437) ) ),
    inference(resolution,[status(thm)],[c_255,c_192])).

tff(c_270,plain,(
    ! [A_438] :
      ( ~ v2_pre_topc(A_438)
      | ~ v4_tex_2('#skF_3',A_438)
      | v2_struct_0(A_438)
      | ~ m1_pre_topc('#skF_3',A_438)
      | ~ l1_pre_topc(A_438) ) ),
    inference(resolution,[status(thm)],[c_133,c_260])).

tff(c_277,plain,
    ( ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_270])).

tff(c_281,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_68,c_277])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_281])).

tff(c_285,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_311,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_306,c_285])).

tff(c_316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_311])).

tff(c_317,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_40,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_72,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_454,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_72])).

tff(c_455,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_454])).

tff(c_11317,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_11311,c_455])).

tff(c_11325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_11317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.48/4.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.48/4.33  
% 11.48/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.48/4.34  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.48/4.34  
% 11.48/4.34  %Foreground sorts:
% 11.48/4.34  
% 11.48/4.34  
% 11.48/4.34  %Background operators:
% 11.48/4.34  
% 11.48/4.34  
% 11.48/4.34  %Foreground operators:
% 11.48/4.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.48/4.34  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 11.48/4.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.48/4.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.48/4.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.48/4.34  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 11.48/4.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.48/4.34  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 11.48/4.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.48/4.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.48/4.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 11.48/4.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.48/4.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.48/4.34  tff('#skF_5', type, '#skF_5': $i).
% 11.48/4.34  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 11.48/4.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.48/4.34  tff('#skF_6', type, '#skF_6': $i).
% 11.48/4.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.48/4.34  tff('#skF_2', type, '#skF_2': $i).
% 11.48/4.34  tff('#skF_3', type, '#skF_3': $i).
% 11.48/4.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.48/4.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.48/4.34  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 11.48/4.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.48/4.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.48/4.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.48/4.34  tff('#skF_4', type, '#skF_4': $i).
% 11.48/4.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.48/4.34  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 11.48/4.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.48/4.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.48/4.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.48/4.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.48/4.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.48/4.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.48/4.34  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 11.48/4.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.48/4.34  
% 11.48/4.36  tff(f_208, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 11.48/4.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.48/4.36  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, A) => (![C]: (m1_subset_1(C, A) => (![D]: (m1_subset_1(D, A) => (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, A) => (![I]: (m1_subset_1(I, A) => (~(A = k1_xboole_0) => m1_subset_1(k6_enumset1(B, C, D, E, F, G, H, I), k1_zfmisc_1(A))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_subset_1)).
% 11.48/4.36  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 11.48/4.36  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 11.48/4.36  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 11.48/4.36  tff(f_116, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 11.48/4.36  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 11.48/4.36  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.48/4.36  tff(f_30, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.48/4.36  tff(f_32, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 11.48/4.36  tff(f_34, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 11.48/4.36  tff(f_36, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 11.48/4.36  tff(f_38, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 11.48/4.36  tff(f_40, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 11.48/4.36  tff(f_169, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 11.48/4.36  tff(f_75, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.48/4.36  tff(c_42, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_46, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_71, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 11.48/4.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.48/4.36  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_563, plain, (![B_552, C_551, F_557, E_555, I_556, G_549, H_554, A_553, D_550]: (m1_subset_1(k6_enumset1(B_552, C_551, D_550, E_555, F_557, G_549, H_554, I_556), k1_zfmisc_1(A_553)) | k1_xboole_0=A_553 | ~m1_subset_1(I_556, A_553) | ~m1_subset_1(H_554, A_553) | ~m1_subset_1(G_549, A_553) | ~m1_subset_1(F_557, A_553) | ~m1_subset_1(E_555, A_553) | ~m1_subset_1(D_550, A_553) | ~m1_subset_1(C_551, A_553) | ~m1_subset_1(B_552, A_553))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.48/4.36  tff(c_22, plain, (![C_294, A_288, B_292]: (m1_subset_1(C_294, k1_zfmisc_1(u1_struct_0(A_288))) | ~m1_subset_1(C_294, k1_zfmisc_1(u1_struct_0(B_292))) | ~m1_pre_topc(B_292, A_288) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.48/4.36  tff(c_5093, plain, (![I_1158, F_1163, A_1164, B_1159, G_1161, D_1162, H_1156, C_1157, B_1155, E_1160]: (m1_subset_1(k6_enumset1(B_1155, C_1157, D_1162, E_1160, F_1163, G_1161, H_1156, I_1158), k1_zfmisc_1(u1_struct_0(A_1164))) | ~m1_pre_topc(B_1159, A_1164) | ~l1_pre_topc(A_1164) | u1_struct_0(B_1159)=k1_xboole_0 | ~m1_subset_1(I_1158, u1_struct_0(B_1159)) | ~m1_subset_1(H_1156, u1_struct_0(B_1159)) | ~m1_subset_1(G_1161, u1_struct_0(B_1159)) | ~m1_subset_1(F_1163, u1_struct_0(B_1159)) | ~m1_subset_1(E_1160, u1_struct_0(B_1159)) | ~m1_subset_1(D_1162, u1_struct_0(B_1159)) | ~m1_subset_1(C_1157, u1_struct_0(B_1159)) | ~m1_subset_1(B_1155, u1_struct_0(B_1159)))), inference(resolution, [status(thm)], [c_563, c_22])).
% 11.48/4.36  tff(c_5095, plain, (![I_1158, F_1163, G_1161, D_1162, H_1156, C_1157, B_1155, E_1160]: (m1_subset_1(k6_enumset1(B_1155, C_1157, D_1162, E_1160, F_1163, G_1161, H_1156, I_1158), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(I_1158, u1_struct_0('#skF_3')) | ~m1_subset_1(H_1156, u1_struct_0('#skF_3')) | ~m1_subset_1(G_1161, u1_struct_0('#skF_3')) | ~m1_subset_1(F_1163, u1_struct_0('#skF_3')) | ~m1_subset_1(E_1160, u1_struct_0('#skF_3')) | ~m1_subset_1(D_1162, u1_struct_0('#skF_3')) | ~m1_subset_1(C_1157, u1_struct_0('#skF_3')) | ~m1_subset_1(B_1155, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_58, c_5093])).
% 11.48/4.36  tff(c_5098, plain, (![I_1158, F_1163, G_1161, D_1162, H_1156, C_1157, B_1155, E_1160]: (m1_subset_1(k6_enumset1(B_1155, C_1157, D_1162, E_1160, F_1163, G_1161, H_1156, I_1158), k1_zfmisc_1(u1_struct_0('#skF_2'))) | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(I_1158, u1_struct_0('#skF_3')) | ~m1_subset_1(H_1156, u1_struct_0('#skF_3')) | ~m1_subset_1(G_1161, u1_struct_0('#skF_3')) | ~m1_subset_1(F_1163, u1_struct_0('#skF_3')) | ~m1_subset_1(E_1160, u1_struct_0('#skF_3')) | ~m1_subset_1(D_1162, u1_struct_0('#skF_3')) | ~m1_subset_1(C_1157, u1_struct_0('#skF_3')) | ~m1_subset_1(B_1155, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5095])).
% 11.48/4.36  tff(c_5208, plain, (u1_struct_0('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5098])).
% 11.48/4.36  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_60, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_110, plain, (![A_378, B_379]: (k6_domain_1(A_378, B_379)=k1_tarski(B_379) | ~m1_subset_1(B_379, A_378) | v1_xboole_0(A_378))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.48/4.36  tff(c_122, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_110])).
% 11.48/4.36  tff(c_323, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_122])).
% 11.48/4.36  tff(c_26, plain, (![B_299, A_297]: (m1_subset_1(u1_struct_0(B_299), k1_zfmisc_1(u1_struct_0(A_297))) | ~m1_pre_topc(B_299, A_297) | ~l1_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.48/4.36  tff(c_424, plain, (![B_490, A_491]: (v3_tex_2(u1_struct_0(B_490), A_491) | ~m1_subset_1(u1_struct_0(B_490), k1_zfmisc_1(u1_struct_0(A_491))) | ~v4_tex_2(B_490, A_491) | ~m1_pre_topc(B_490, A_491) | ~l1_pre_topc(A_491) | v2_struct_0(A_491))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.48/4.36  tff(c_429, plain, (![B_492, A_493]: (v3_tex_2(u1_struct_0(B_492), A_493) | ~v4_tex_2(B_492, A_493) | v2_struct_0(A_493) | ~m1_pre_topc(B_492, A_493) | ~l1_pre_topc(A_493))), inference(resolution, [status(thm)], [c_26, c_424])).
% 11.48/4.36  tff(c_372, plain, (![B_470, A_471]: (~v3_tex_2(B_470, A_471) | ~m1_subset_1(B_470, k1_zfmisc_1(u1_struct_0(A_471))) | ~v1_xboole_0(B_470) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | v2_struct_0(A_471))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.48/4.36  tff(c_376, plain, (![B_299, A_297]: (~v3_tex_2(u1_struct_0(B_299), A_297) | ~v1_xboole_0(u1_struct_0(B_299)) | ~v2_pre_topc(A_297) | v2_struct_0(A_297) | ~m1_pre_topc(B_299, A_297) | ~l1_pre_topc(A_297))), inference(resolution, [status(thm)], [c_26, c_372])).
% 11.48/4.36  tff(c_434, plain, (![B_494, A_495]: (~v1_xboole_0(u1_struct_0(B_494)) | ~v2_pre_topc(A_495) | ~v4_tex_2(B_494, A_495) | v2_struct_0(A_495) | ~m1_pre_topc(B_494, A_495) | ~l1_pre_topc(A_495))), inference(resolution, [status(thm)], [c_429, c_376])).
% 11.48/4.36  tff(c_438, plain, (![A_496]: (~v2_pre_topc(A_496) | ~v4_tex_2('#skF_3', A_496) | v2_struct_0(A_496) | ~m1_pre_topc('#skF_3', A_496) | ~l1_pre_topc(A_496))), inference(resolution, [status(thm)], [c_323, c_434])).
% 11.48/4.36  tff(c_445, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_438])).
% 11.48/4.36  tff(c_449, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_68, c_445])).
% 11.48/4.36  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_449])).
% 11.48/4.36  tff(c_453, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_122])).
% 11.48/4.36  tff(c_5217, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5208, c_453])).
% 11.48/4.36  tff(c_5224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_5217])).
% 11.48/4.36  tff(c_5226, plain, (u1_struct_0('#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_5098])).
% 11.48/4.36  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_54, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_52, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_48, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 11.48/4.36  tff(c_6, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 11.48/4.36  tff(c_8, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.48/4.36  tff(c_10, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.48/4.36  tff(c_12, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.48/4.36  tff(c_14, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.48/4.36  tff(c_16, plain, (![G_28, E_26, F_27, A_22, B_23, D_25, C_24]: (k6_enumset1(A_22, A_22, B_23, C_24, D_25, E_26, F_27, G_28)=k5_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.48/4.36  tff(c_649, plain, (![B_587, D_586, E_582, G_585, F_584, A_580, C_581, A_583]: (m1_subset_1(k5_enumset1(A_580, B_587, C_581, D_586, E_582, F_584, G_585), k1_zfmisc_1(A_583)) | k1_xboole_0=A_583 | ~m1_subset_1(G_585, A_583) | ~m1_subset_1(F_584, A_583) | ~m1_subset_1(E_582, A_583) | ~m1_subset_1(D_586, A_583) | ~m1_subset_1(C_581, A_583) | ~m1_subset_1(B_587, A_583) | ~m1_subset_1(A_580, A_583) | ~m1_subset_1(A_580, A_583))), inference(superposition, [status(thm), theory('equality')], [c_16, c_563])).
% 11.48/4.36  tff(c_728, plain, (![B_606, C_611, A_610, F_605, E_607, D_609, A_608]: (m1_subset_1(k4_enumset1(A_608, B_606, C_611, D_609, E_607, F_605), k1_zfmisc_1(A_610)) | k1_xboole_0=A_610 | ~m1_subset_1(F_605, A_610) | ~m1_subset_1(E_607, A_610) | ~m1_subset_1(D_609, A_610) | ~m1_subset_1(C_611, A_610) | ~m1_subset_1(B_606, A_610) | ~m1_subset_1(A_608, A_610) | ~m1_subset_1(A_608, A_610) | ~m1_subset_1(A_608, A_610))), inference(superposition, [status(thm), theory('equality')], [c_14, c_649])).
% 11.48/4.36  tff(c_789, plain, (![D_623, A_621, B_622, E_624, C_620, A_619]: (m1_subset_1(k3_enumset1(A_621, B_622, C_620, D_623, E_624), k1_zfmisc_1(A_619)) | k1_xboole_0=A_619 | ~m1_subset_1(E_624, A_619) | ~m1_subset_1(D_623, A_619) | ~m1_subset_1(C_620, A_619) | ~m1_subset_1(B_622, A_619) | ~m1_subset_1(A_621, A_619) | ~m1_subset_1(A_621, A_619) | ~m1_subset_1(A_621, A_619) | ~m1_subset_1(A_621, A_619))), inference(superposition, [status(thm), theory('equality')], [c_12, c_728])).
% 11.48/4.36  tff(c_4871, plain, (![D_1118, A_1121, C_1120, A_1122, B_1119]: (m1_subset_1(k2_enumset1(A_1122, B_1119, C_1120, D_1118), k1_zfmisc_1(A_1121)) | k1_xboole_0=A_1121 | ~m1_subset_1(D_1118, A_1121) | ~m1_subset_1(C_1120, A_1121) | ~m1_subset_1(B_1119, A_1121) | ~m1_subset_1(A_1122, A_1121) | ~m1_subset_1(A_1122, A_1121) | ~m1_subset_1(A_1122, A_1121) | ~m1_subset_1(A_1122, A_1121) | ~m1_subset_1(A_1122, A_1121))), inference(superposition, [status(thm), theory('equality')], [c_10, c_789])).
% 11.48/4.36  tff(c_5109, plain, (![A_1167, B_1168, C_1169, A_1170]: (m1_subset_1(k1_enumset1(A_1167, B_1168, C_1169), k1_zfmisc_1(A_1170)) | k1_xboole_0=A_1170 | ~m1_subset_1(C_1169, A_1170) | ~m1_subset_1(B_1168, A_1170) | ~m1_subset_1(A_1167, A_1170) | ~m1_subset_1(A_1167, A_1170) | ~m1_subset_1(A_1167, A_1170) | ~m1_subset_1(A_1167, A_1170) | ~m1_subset_1(A_1167, A_1170) | ~m1_subset_1(A_1167, A_1170))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4871])).
% 11.48/4.36  tff(c_6920, plain, (![A_1372, B_1373, A_1374]: (m1_subset_1(k2_tarski(A_1372, B_1373), k1_zfmisc_1(A_1374)) | k1_xboole_0=A_1374 | ~m1_subset_1(B_1373, A_1374) | ~m1_subset_1(A_1372, A_1374) | ~m1_subset_1(A_1372, A_1374) | ~m1_subset_1(A_1372, A_1374) | ~m1_subset_1(A_1372, A_1374) | ~m1_subset_1(A_1372, A_1374) | ~m1_subset_1(A_1372, A_1374) | ~m1_subset_1(A_1372, A_1374))), inference(superposition, [status(thm), theory('equality')], [c_6, c_5109])).
% 11.48/4.36  tff(c_7895, plain, (![A_1490, A_1491]: (m1_subset_1(k1_tarski(A_1490), k1_zfmisc_1(A_1491)) | k1_xboole_0=A_1491 | ~m1_subset_1(A_1490, A_1491) | ~m1_subset_1(A_1490, A_1491) | ~m1_subset_1(A_1490, A_1491) | ~m1_subset_1(A_1490, A_1491) | ~m1_subset_1(A_1490, A_1491) | ~m1_subset_1(A_1490, A_1491) | ~m1_subset_1(A_1490, A_1491) | ~m1_subset_1(A_1490, A_1491))), inference(superposition, [status(thm), theory('equality')], [c_4, c_6920])).
% 11.48/4.36  tff(c_66, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_5315, plain, (![C_1178, B_1180, A_1182, B_1179, A_1181]: (m1_subset_1(k1_enumset1(A_1182, B_1180, C_1178), k1_zfmisc_1(u1_struct_0(A_1181))) | ~m1_pre_topc(B_1179, A_1181) | ~l1_pre_topc(A_1181) | u1_struct_0(B_1179)=k1_xboole_0 | ~m1_subset_1(C_1178, u1_struct_0(B_1179)) | ~m1_subset_1(B_1180, u1_struct_0(B_1179)) | ~m1_subset_1(A_1182, u1_struct_0(B_1179)))), inference(resolution, [status(thm)], [c_5109, c_22])).
% 11.48/4.36  tff(c_5317, plain, (![A_1182, B_1180, C_1178]: (m1_subset_1(k1_enumset1(A_1182, B_1180, C_1178), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(C_1178, u1_struct_0('#skF_3')) | ~m1_subset_1(B_1180, u1_struct_0('#skF_3')) | ~m1_subset_1(A_1182, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_58, c_5315])).
% 11.48/4.36  tff(c_5320, plain, (![A_1182, B_1180, C_1178]: (m1_subset_1(k1_enumset1(A_1182, B_1180, C_1178), k1_zfmisc_1(u1_struct_0('#skF_2'))) | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(C_1178, u1_struct_0('#skF_3')) | ~m1_subset_1(B_1180, u1_struct_0('#skF_3')) | ~m1_subset_1(A_1182, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5317])).
% 11.48/4.36  tff(c_5326, plain, (![A_1187, B_1188, C_1189]: (m1_subset_1(k1_enumset1(A_1187, B_1188, C_1189), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(C_1189, u1_struct_0('#skF_3')) | ~m1_subset_1(B_1188, u1_struct_0('#skF_3')) | ~m1_subset_1(A_1187, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_5226, c_5320])).
% 11.48/4.36  tff(c_5372, plain, (![A_1190, B_1191]: (m1_subset_1(k2_tarski(A_1190, B_1191), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_1191, u1_struct_0('#skF_3')) | ~m1_subset_1(A_1190, u1_struct_0('#skF_3')) | ~m1_subset_1(A_1190, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6, c_5326])).
% 11.48/4.36  tff(c_5429, plain, (![A_1198]: (m1_subset_1(k1_tarski(A_1198), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(A_1198, u1_struct_0('#skF_3')) | ~m1_subset_1(A_1198, u1_struct_0('#skF_3')) | ~m1_subset_1(A_1198, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5372])).
% 11.48/4.36  tff(c_38, plain, (![A_313, B_329, C_337, E_343]: (k8_relset_1(u1_struct_0(A_313), u1_struct_0(B_329), C_337, E_343)=k2_pre_topc(A_313, E_343) | ~m1_subset_1(E_343, k1_zfmisc_1(u1_struct_0(A_313))) | ~m1_subset_1(E_343, k1_zfmisc_1(u1_struct_0(B_329))) | ~v3_borsuk_1(C_337, A_313, B_329) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_313), u1_struct_0(B_329)))) | ~v5_pre_topc(C_337, A_313, B_329) | ~v1_funct_2(C_337, u1_struct_0(A_313), u1_struct_0(B_329)) | ~v1_funct_1(C_337) | ~m1_pre_topc(B_329, A_313) | ~v4_tex_2(B_329, A_313) | v2_struct_0(B_329) | ~l1_pre_topc(A_313) | ~v3_tdlat_3(A_313) | ~v2_pre_topc(A_313) | v2_struct_0(A_313))), inference(cnfTransformation, [status(thm)], [f_169])).
% 11.48/4.36  tff(c_5443, plain, (![B_329, C_337, A_1198]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_329), C_337, k1_tarski(A_1198))=k2_pre_topc('#skF_2', k1_tarski(A_1198)) | ~m1_subset_1(k1_tarski(A_1198), k1_zfmisc_1(u1_struct_0(B_329))) | ~v3_borsuk_1(C_337, '#skF_2', B_329) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_329)))) | ~v5_pre_topc(C_337, '#skF_2', B_329) | ~v1_funct_2(C_337, u1_struct_0('#skF_2'), u1_struct_0(B_329)) | ~v1_funct_1(C_337) | ~m1_pre_topc(B_329, '#skF_2') | ~v4_tex_2(B_329, '#skF_2') | v2_struct_0(B_329) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(A_1198, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5429, c_38])).
% 11.48/4.36  tff(c_5463, plain, (![B_329, C_337, A_1198]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_329), C_337, k1_tarski(A_1198))=k2_pre_topc('#skF_2', k1_tarski(A_1198)) | ~m1_subset_1(k1_tarski(A_1198), k1_zfmisc_1(u1_struct_0(B_329))) | ~v3_borsuk_1(C_337, '#skF_2', B_329) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_329)))) | ~v5_pre_topc(C_337, '#skF_2', B_329) | ~v1_funct_2(C_337, u1_struct_0('#skF_2'), u1_struct_0(B_329)) | ~v1_funct_1(C_337) | ~m1_pre_topc(B_329, '#skF_2') | ~v4_tex_2(B_329, '#skF_2') | v2_struct_0(B_329) | v2_struct_0('#skF_2') | ~m1_subset_1(A_1198, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_5443])).
% 11.48/4.36  tff(c_5464, plain, (![B_329, C_337, A_1198]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_329), C_337, k1_tarski(A_1198))=k2_pre_topc('#skF_2', k1_tarski(A_1198)) | ~m1_subset_1(k1_tarski(A_1198), k1_zfmisc_1(u1_struct_0(B_329))) | ~v3_borsuk_1(C_337, '#skF_2', B_329) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_329)))) | ~v5_pre_topc(C_337, '#skF_2', B_329) | ~v1_funct_2(C_337, u1_struct_0('#skF_2'), u1_struct_0(B_329)) | ~v1_funct_1(C_337) | ~m1_pre_topc(B_329, '#skF_2') | ~v4_tex_2(B_329, '#skF_2') | v2_struct_0(B_329) | ~m1_subset_1(A_1198, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_70, c_5463])).
% 11.48/4.36  tff(c_11272, plain, (![B_2027, C_2028, A_2029]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_2027), C_2028, k1_tarski(A_2029))=k2_pre_topc('#skF_2', k1_tarski(A_2029)) | ~v3_borsuk_1(C_2028, '#skF_2', B_2027) | ~m1_subset_1(C_2028, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_2027)))) | ~v5_pre_topc(C_2028, '#skF_2', B_2027) | ~v1_funct_2(C_2028, u1_struct_0('#skF_2'), u1_struct_0(B_2027)) | ~v1_funct_1(C_2028) | ~m1_pre_topc(B_2027, '#skF_2') | ~v4_tex_2(B_2027, '#skF_2') | v2_struct_0(B_2027) | ~m1_subset_1(A_2029, u1_struct_0('#skF_3')) | u1_struct_0(B_2027)=k1_xboole_0 | ~m1_subset_1(A_2029, u1_struct_0(B_2027)))), inference(resolution, [status(thm)], [c_7895, c_5464])).
% 11.48/4.36  tff(c_11298, plain, (![A_2029]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_2029))=k2_pre_topc('#skF_2', k1_tarski(A_2029)) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(A_2029, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_50, c_11272])).
% 11.48/4.36  tff(c_11309, plain, (![A_2029]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_2029))=k2_pre_topc('#skF_2', k1_tarski(A_2029)) | v2_struct_0('#skF_3') | u1_struct_0('#skF_3')=k1_xboole_0 | ~m1_subset_1(A_2029, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_48, c_11298])).
% 11.48/4.36  tff(c_11311, plain, (![A_2030]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski(A_2030))=k2_pre_topc('#skF_2', k1_tarski(A_2030)) | ~m1_subset_1(A_2030, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_5226, c_62, c_11309])).
% 11.48/4.36  tff(c_452, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_122])).
% 11.48/4.36  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_121, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_110])).
% 11.48/4.36  tff(c_123, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_121])).
% 11.48/4.36  tff(c_286, plain, (![B_439, A_440]: (m1_subset_1(u1_struct_0(B_439), k1_zfmisc_1(u1_struct_0(A_440))) | ~m1_pre_topc(B_439, A_440) | ~l1_pre_topc(A_440))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.48/4.36  tff(c_20, plain, (![B_287, A_285]: (v1_xboole_0(B_287) | ~m1_subset_1(B_287, k1_zfmisc_1(A_285)) | ~v1_xboole_0(A_285))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.48/4.36  tff(c_299, plain, (![B_441, A_442]: (v1_xboole_0(u1_struct_0(B_441)) | ~v1_xboole_0(u1_struct_0(A_442)) | ~m1_pre_topc(B_441, A_442) | ~l1_pre_topc(A_442))), inference(resolution, [status(thm)], [c_286, c_20])).
% 11.48/4.36  tff(c_301, plain, (![B_441]: (v1_xboole_0(u1_struct_0(B_441)) | ~m1_pre_topc(B_441, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_123, c_299])).
% 11.48/4.36  tff(c_306, plain, (![B_443]: (v1_xboole_0(u1_struct_0(B_443)) | ~m1_pre_topc(B_443, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_301])).
% 11.48/4.36  tff(c_133, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_122])).
% 11.48/4.36  tff(c_250, plain, (![B_432, A_433]: (v3_tex_2(u1_struct_0(B_432), A_433) | ~m1_subset_1(u1_struct_0(B_432), k1_zfmisc_1(u1_struct_0(A_433))) | ~v4_tex_2(B_432, A_433) | ~m1_pre_topc(B_432, A_433) | ~l1_pre_topc(A_433) | v2_struct_0(A_433))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.48/4.36  tff(c_255, plain, (![B_434, A_435]: (v3_tex_2(u1_struct_0(B_434), A_435) | ~v4_tex_2(B_434, A_435) | v2_struct_0(A_435) | ~m1_pre_topc(B_434, A_435) | ~l1_pre_topc(A_435))), inference(resolution, [status(thm)], [c_26, c_250])).
% 11.48/4.36  tff(c_188, plain, (![B_409, A_410]: (~v3_tex_2(B_409, A_410) | ~m1_subset_1(B_409, k1_zfmisc_1(u1_struct_0(A_410))) | ~v1_xboole_0(B_409) | ~l1_pre_topc(A_410) | ~v2_pre_topc(A_410) | v2_struct_0(A_410))), inference(cnfTransformation, [status(thm)], [f_131])).
% 11.48/4.36  tff(c_192, plain, (![B_299, A_297]: (~v3_tex_2(u1_struct_0(B_299), A_297) | ~v1_xboole_0(u1_struct_0(B_299)) | ~v2_pre_topc(A_297) | v2_struct_0(A_297) | ~m1_pre_topc(B_299, A_297) | ~l1_pre_topc(A_297))), inference(resolution, [status(thm)], [c_26, c_188])).
% 11.48/4.36  tff(c_260, plain, (![B_436, A_437]: (~v1_xboole_0(u1_struct_0(B_436)) | ~v2_pre_topc(A_437) | ~v4_tex_2(B_436, A_437) | v2_struct_0(A_437) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437))), inference(resolution, [status(thm)], [c_255, c_192])).
% 11.48/4.36  tff(c_270, plain, (![A_438]: (~v2_pre_topc(A_438) | ~v4_tex_2('#skF_3', A_438) | v2_struct_0(A_438) | ~m1_pre_topc('#skF_3', A_438) | ~l1_pre_topc(A_438))), inference(resolution, [status(thm)], [c_133, c_260])).
% 11.48/4.36  tff(c_277, plain, (~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_270])).
% 11.48/4.36  tff(c_281, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_68, c_277])).
% 11.48/4.36  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_281])).
% 11.48/4.36  tff(c_285, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_122])).
% 11.48/4.36  tff(c_311, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_306, c_285])).
% 11.48/4.36  tff(c_316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_311])).
% 11.48/4.36  tff(c_317, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_121])).
% 11.48/4.36  tff(c_40, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 11.48/4.36  tff(c_72, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 11.48/4.36  tff(c_454, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_72])).
% 11.48/4.36  tff(c_455, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_454])).
% 11.48/4.36  tff(c_11317, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11311, c_455])).
% 11.48/4.36  tff(c_11325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_11317])).
% 11.48/4.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.48/4.36  
% 11.48/4.36  Inference rules
% 11.48/4.36  ----------------------
% 11.48/4.36  #Ref     : 0
% 11.48/4.36  #Sup     : 2610
% 11.48/4.36  #Fact    : 0
% 11.48/4.36  #Define  : 0
% 11.48/4.36  #Split   : 27
% 11.48/4.36  #Chain   : 0
% 11.48/4.36  #Close   : 0
% 11.48/4.36  
% 11.48/4.36  Ordering : KBO
% 11.48/4.36  
% 11.48/4.36  Simplification rules
% 11.48/4.36  ----------------------
% 11.48/4.36  #Subsume      : 438
% 11.48/4.36  #Demod        : 1350
% 11.48/4.36  #Tautology    : 587
% 11.48/4.36  #SimpNegUnit  : 356
% 11.48/4.36  #BackRed      : 139
% 11.48/4.36  
% 11.48/4.36  #Partial instantiations: 0
% 11.48/4.36  #Strategies tried      : 1
% 11.48/4.36  
% 11.48/4.36  Timing (in seconds)
% 11.48/4.36  ----------------------
% 11.48/4.36  Preprocessing        : 0.42
% 11.48/4.36  Parsing              : 0.20
% 11.48/4.36  CNF conversion       : 0.05
% 11.48/4.36  Main loop            : 3.11
% 11.48/4.36  Inferencing          : 0.86
% 11.48/4.36  Reduction            : 0.99
% 11.48/4.36  Demodulation         : 0.69
% 11.48/4.36  BG Simplification    : 0.11
% 11.48/4.36  Subsumption          : 0.92
% 11.48/4.36  Abstraction          : 0.17
% 11.48/4.36  MUC search           : 0.00
% 11.48/4.36  Cooper               : 0.00
% 11.48/4.36  Total                : 3.58
% 11.48/4.36  Index Insertion      : 0.00
% 11.48/4.37  Index Deletion       : 0.00
% 11.48/4.37  Index Matching       : 0.00
% 11.48/4.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
