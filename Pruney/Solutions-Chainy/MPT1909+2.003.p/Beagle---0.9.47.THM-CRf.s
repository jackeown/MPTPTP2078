%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:37 EST 2020

% Result     : Theorem 12.80s
% Output     : CNFRefutation 13.16s
% Verified   : 
% Statistics : Number of formulae       :  279 (4549 expanded)
%              Number of leaves         :   57 (1575 expanded)
%              Depth                    :   29
%              Number of atoms          :  876 (24017 expanded)
%              Number of equality atoms :   94 (2384 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > v2_tex_2 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_297,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_161,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tdlat_3(B)
           => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc18_tex_2)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & v4_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc35_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_181,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(f_220,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_197,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tex_2)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_258,axiom,(
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

tff(c_86,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_88,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_82,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_114,plain,(
    ! [B_123,A_124] :
      ( l1_pre_topc(B_123)
      | ~ m1_pre_topc(B_123,A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_120,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_114])).

tff(c_124,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_120])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_36] :
      ( m1_pre_topc(A_36,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7146,plain,(
    ! [C_582,A_583,B_584] :
      ( m1_subset_1(C_582,k1_zfmisc_1(u1_struct_0(A_583)))
      | ~ m1_subset_1(C_582,k1_zfmisc_1(u1_struct_0(B_584)))
      | ~ m1_pre_topc(B_584,A_583)
      | ~ l1_pre_topc(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7258,plain,(
    ! [A_591,A_592,B_593] :
      ( m1_subset_1(A_591,k1_zfmisc_1(u1_struct_0(A_592)))
      | ~ m1_pre_topc(B_593,A_592)
      | ~ l1_pre_topc(A_592)
      | ~ r1_tarski(A_591,u1_struct_0(B_593)) ) ),
    inference(resolution,[status(thm)],[c_14,c_7146])).

tff(c_7262,plain,(
    ! [A_591] :
      ( m1_subset_1(A_591,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_591,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_82,c_7258])).

tff(c_7267,plain,(
    ! [A_594] :
      ( m1_subset_1(A_594,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_594,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7262])).

tff(c_46,plain,(
    ! [B_45,A_43] :
      ( v1_tops_1(B_45,A_43)
      | k2_pre_topc(A_43,B_45) != u1_struct_0(A_43)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7281,plain,(
    ! [A_594] :
      ( v1_tops_1(A_594,'#skF_2')
      | k2_pre_topc('#skF_2',A_594) != u1_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_594,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7267,c_46])).

tff(c_7422,plain,(
    ! [A_601] :
      ( v1_tops_1(A_601,'#skF_2')
      | k2_pre_topc('#skF_2',A_601) != u1_struct_0('#skF_2')
      | ~ r1_tarski(A_601,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7281])).

tff(c_7448,plain,
    ( v1_tops_1(u1_struct_0('#skF_3'),'#skF_2')
    | k2_pre_topc('#skF_2',u1_struct_0('#skF_3')) != u1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_7422])).

tff(c_7471,plain,(
    k2_pre_topc('#skF_2',u1_struct_0('#skF_3')) != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7448])).

tff(c_48,plain,(
    ! [A_43,B_45] :
      ( k2_pre_topc(A_43,B_45) = u1_struct_0(A_43)
      | ~ v1_tops_1(B_45,A_43)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7275,plain,(
    ! [A_594] :
      ( k2_pre_topc('#skF_2',A_594) = u1_struct_0('#skF_2')
      | ~ v1_tops_1(A_594,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_594,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7267,c_48])).

tff(c_7601,plain,(
    ! [A_609] :
      ( k2_pre_topc('#skF_2',A_609) = u1_struct_0('#skF_2')
      | ~ v1_tops_1(A_609,'#skF_2')
      | ~ r1_tarski(A_609,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7275])).

tff(c_7617,plain,
    ( k2_pre_topc('#skF_2',u1_struct_0('#skF_3')) = u1_struct_0('#skF_2')
    | ~ v1_tops_1(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_7601])).

tff(c_7629,plain,(
    ~ v1_tops_1(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_7471,c_7617])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_6828,plain,(
    ! [B_533,A_534] :
      ( v3_tdlat_3(B_533)
      | ~ v1_tdlat_3(B_533)
      | ~ m1_pre_topc(B_533,A_534)
      | ~ l1_pre_topc(A_534)
      | v2_struct_0(A_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6834,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_6828])).

tff(c_6838,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_6834])).

tff(c_6839,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ v1_tdlat_3('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_6838])).

tff(c_6840,plain,(
    ~ v1_tdlat_3('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6839])).

tff(c_84,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_6866,plain,(
    ! [B_543,A_544] :
      ( v1_tdlat_3(B_543)
      | ~ v4_tex_2(B_543,A_544)
      | v2_struct_0(B_543)
      | ~ m1_pre_topc(B_543,A_544)
      | ~ l1_pre_topc(A_544)
      | v2_struct_0(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_6869,plain,
    ( v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_6866])).

tff(c_6872,plain,
    ( v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_6869])).

tff(c_6874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_86,c_6840,c_6872])).

tff(c_6876,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6839])).

tff(c_92,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_159,plain,(
    ! [B_140,A_141] :
      ( v2_pre_topc(B_140)
      | ~ m1_pre_topc(B_140,A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_165,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_159])).

tff(c_169,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_165])).

tff(c_6875,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(splitRight,[status(thm)],[c_6839])).

tff(c_36,plain,(
    ! [B_35,A_33] :
      ( m1_subset_1(u1_struct_0(B_35),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7657,plain,(
    ! [B_611,A_612] :
      ( v2_tex_2(u1_struct_0(B_611),A_612)
      | ~ v1_tdlat_3(B_611)
      | ~ m1_subset_1(u1_struct_0(B_611),k1_zfmisc_1(u1_struct_0(A_612)))
      | ~ m1_pre_topc(B_611,A_612)
      | v2_struct_0(B_611)
      | ~ l1_pre_topc(A_612)
      | v2_struct_0(A_612) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_7672,plain,(
    ! [B_35,A_33] :
      ( v2_tex_2(u1_struct_0(B_35),A_33)
      | ~ v1_tdlat_3(B_35)
      | v2_struct_0(B_35)
      | v2_struct_0(A_33)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_36,c_7657])).

tff(c_7394,plain,(
    ! [B_599,A_600] :
      ( r1_tarski(B_599,'#skF_1'(A_600,B_599))
      | ~ v2_tex_2(B_599,A_600)
      | ~ m1_subset_1(B_599,k1_zfmisc_1(u1_struct_0(A_600)))
      | ~ l1_pre_topc(A_600)
      | ~ v3_tdlat_3(A_600)
      | ~ v2_pre_topc(A_600)
      | v2_struct_0(A_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_9760,plain,(
    ! [A_758,A_759] :
      ( r1_tarski(A_758,'#skF_1'(A_759,A_758))
      | ~ v2_tex_2(A_758,A_759)
      | ~ l1_pre_topc(A_759)
      | ~ v3_tdlat_3(A_759)
      | ~ v2_pre_topc(A_759)
      | v2_struct_0(A_759)
      | ~ r1_tarski(A_758,u1_struct_0(A_759)) ) ),
    inference(resolution,[status(thm)],[c_14,c_7394])).

tff(c_9801,plain,(
    ! [A_759] :
      ( r1_tarski(u1_struct_0(A_759),'#skF_1'(A_759,u1_struct_0(A_759)))
      | ~ v2_tex_2(u1_struct_0(A_759),A_759)
      | ~ l1_pre_topc(A_759)
      | ~ v3_tdlat_3(A_759)
      | ~ v2_pre_topc(A_759)
      | v2_struct_0(A_759) ) ),
    inference(resolution,[status(thm)],[c_6,c_9760])).

tff(c_8197,plain,(
    ! [A_640,B_641] :
      ( m1_subset_1('#skF_1'(A_640,B_641),k1_zfmisc_1(u1_struct_0(A_640)))
      | ~ v2_tex_2(B_641,A_640)
      | ~ m1_subset_1(B_641,k1_zfmisc_1(u1_struct_0(A_640)))
      | ~ l1_pre_topc(A_640)
      | ~ v3_tdlat_3(A_640)
      | ~ v2_pre_topc(A_640)
      | v2_struct_0(A_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10439,plain,(
    ! [A_776,B_777] :
      ( r1_tarski('#skF_1'(A_776,B_777),u1_struct_0(A_776))
      | ~ v2_tex_2(B_777,A_776)
      | ~ m1_subset_1(B_777,k1_zfmisc_1(u1_struct_0(A_776)))
      | ~ l1_pre_topc(A_776)
      | ~ v3_tdlat_3(A_776)
      | ~ v2_pre_topc(A_776)
      | v2_struct_0(A_776) ) ),
    inference(resolution,[status(thm)],[c_8197,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17791,plain,(
    ! [A_1071,B_1072] :
      ( u1_struct_0(A_1071) = '#skF_1'(A_1071,B_1072)
      | ~ r1_tarski(u1_struct_0(A_1071),'#skF_1'(A_1071,B_1072))
      | ~ v2_tex_2(B_1072,A_1071)
      | ~ m1_subset_1(B_1072,k1_zfmisc_1(u1_struct_0(A_1071)))
      | ~ l1_pre_topc(A_1071)
      | ~ v3_tdlat_3(A_1071)
      | ~ v2_pre_topc(A_1071)
      | v2_struct_0(A_1071) ) ),
    inference(resolution,[status(thm)],[c_10439,c_2])).

tff(c_20106,plain,(
    ! [A_1137] :
      ( '#skF_1'(A_1137,u1_struct_0(A_1137)) = u1_struct_0(A_1137)
      | ~ m1_subset_1(u1_struct_0(A_1137),k1_zfmisc_1(u1_struct_0(A_1137)))
      | ~ v2_tex_2(u1_struct_0(A_1137),A_1137)
      | ~ l1_pre_topc(A_1137)
      | ~ v3_tdlat_3(A_1137)
      | ~ v2_pre_topc(A_1137)
      | v2_struct_0(A_1137) ) ),
    inference(resolution,[status(thm)],[c_9801,c_17791])).

tff(c_20135,plain,(
    ! [A_1137] :
      ( '#skF_1'(A_1137,u1_struct_0(A_1137)) = u1_struct_0(A_1137)
      | ~ v2_tex_2(u1_struct_0(A_1137),A_1137)
      | ~ l1_pre_topc(A_1137)
      | ~ v3_tdlat_3(A_1137)
      | ~ v2_pre_topc(A_1137)
      | v2_struct_0(A_1137)
      | ~ r1_tarski(u1_struct_0(A_1137),u1_struct_0(A_1137)) ) ),
    inference(resolution,[status(thm)],[c_14,c_20106])).

tff(c_20150,plain,(
    ! [A_1138] :
      ( '#skF_1'(A_1138,u1_struct_0(A_1138)) = u1_struct_0(A_1138)
      | ~ v2_tex_2(u1_struct_0(A_1138),A_1138)
      | ~ l1_pre_topc(A_1138)
      | ~ v3_tdlat_3(A_1138)
      | ~ v2_pre_topc(A_1138)
      | v2_struct_0(A_1138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20135])).

tff(c_20170,plain,(
    ! [A_1139] :
      ( '#skF_1'(A_1139,u1_struct_0(A_1139)) = u1_struct_0(A_1139)
      | ~ v3_tdlat_3(A_1139)
      | ~ v2_pre_topc(A_1139)
      | ~ v1_tdlat_3(A_1139)
      | v2_struct_0(A_1139)
      | ~ m1_pre_topc(A_1139,A_1139)
      | ~ l1_pre_topc(A_1139) ) ),
    inference(resolution,[status(thm)],[c_7672,c_20150])).

tff(c_32,plain,(
    ! [B_32,A_30] :
      ( v1_tops_1(B_32,A_30)
      | k2_pre_topc(A_30,B_32) != k2_struct_0(A_30)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7278,plain,(
    ! [A_594] :
      ( v1_tops_1(A_594,'#skF_2')
      | k2_pre_topc('#skF_2',A_594) != k2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_594,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7267,c_32])).

tff(c_7303,plain,(
    ! [A_594] :
      ( v1_tops_1(A_594,'#skF_2')
      | k2_pre_topc('#skF_2',A_594) != k2_struct_0('#skF_2')
      | ~ r1_tarski(A_594,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_7278])).

tff(c_10457,plain,(
    ! [B_777] :
      ( v1_tops_1('#skF_1'('#skF_3',B_777),'#skF_2')
      | k2_pre_topc('#skF_2','#skF_1'('#skF_3',B_777)) != k2_struct_0('#skF_2')
      | ~ v2_tex_2(B_777,'#skF_3')
      | ~ m1_subset_1(B_777,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10439,c_7303])).

tff(c_10509,plain,(
    ! [B_777] :
      ( v1_tops_1('#skF_1'('#skF_3',B_777),'#skF_2')
      | k2_pre_topc('#skF_2','#skF_1'('#skF_3',B_777)) != k2_struct_0('#skF_2')
      | ~ v2_tex_2(B_777,'#skF_3')
      | ~ m1_subset_1(B_777,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_6875,c_124,c_10457])).

tff(c_11504,plain,(
    ! [B_818] :
      ( v1_tops_1('#skF_1'('#skF_3',B_818),'#skF_2')
      | k2_pre_topc('#skF_2','#skF_1'('#skF_3',B_818)) != k2_struct_0('#skF_2')
      | ~ v2_tex_2(B_818,'#skF_3')
      | ~ m1_subset_1(B_818,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_10509])).

tff(c_11532,plain,(
    ! [B_35] :
      ( v1_tops_1('#skF_1'('#skF_3',u1_struct_0(B_35)),'#skF_2')
      | k2_pre_topc('#skF_2','#skF_1'('#skF_3',u1_struct_0(B_35))) != k2_struct_0('#skF_2')
      | ~ v2_tex_2(u1_struct_0(B_35),'#skF_3')
      | ~ m1_pre_topc(B_35,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_11504])).

tff(c_11562,plain,(
    ! [B_35] :
      ( v1_tops_1('#skF_1'('#skF_3',u1_struct_0(B_35)),'#skF_2')
      | k2_pre_topc('#skF_2','#skF_1'('#skF_3',u1_struct_0(B_35))) != k2_struct_0('#skF_2')
      | ~ v2_tex_2(u1_struct_0(B_35),'#skF_3')
      | ~ m1_pre_topc(B_35,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_11532])).

tff(c_20303,plain,
    ( v1_tops_1(u1_struct_0('#skF_3'),'#skF_2')
    | k2_pre_topc('#skF_2','#skF_1'('#skF_3',u1_struct_0('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20170,c_11562])).

tff(c_20493,plain,
    ( v1_tops_1(u1_struct_0('#skF_3'),'#skF_2')
    | k2_pre_topc('#skF_2','#skF_1'('#skF_3',u1_struct_0('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_6876,c_169,c_6875,c_20303])).

tff(c_20494,plain,
    ( k2_pre_topc('#skF_2','#skF_1'('#skF_3',u1_struct_0('#skF_3'))) != k2_struct_0('#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7629,c_20493])).

tff(c_20563,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20494])).

tff(c_20613,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_20563])).

tff(c_20617,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20613])).

tff(c_20619,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20494])).

tff(c_6980,plain,(
    ! [B_565,A_566] :
      ( v1_tops_1(B_565,A_566)
      | k2_pre_topc(A_566,B_565) != u1_struct_0(A_566)
      | ~ m1_subset_1(B_565,k1_zfmisc_1(u1_struct_0(A_566)))
      | ~ l1_pre_topc(A_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7048,plain,(
    ! [A_572,A_573] :
      ( v1_tops_1(A_572,A_573)
      | k2_pre_topc(A_573,A_572) != u1_struct_0(A_573)
      | ~ l1_pre_topc(A_573)
      | ~ r1_tarski(A_572,u1_struct_0(A_573)) ) ),
    inference(resolution,[status(thm)],[c_14,c_6980])).

tff(c_7069,plain,(
    ! [A_573] :
      ( v1_tops_1(u1_struct_0(A_573),A_573)
      | k2_pre_topc(A_573,u1_struct_0(A_573)) != u1_struct_0(A_573)
      | ~ l1_pre_topc(A_573) ) ),
    inference(resolution,[status(thm)],[c_6,c_7048])).

tff(c_7157,plain,(
    ! [B_35,A_583,A_33] :
      ( m1_subset_1(u1_struct_0(B_35),k1_zfmisc_1(u1_struct_0(A_583)))
      | ~ m1_pre_topc(A_33,A_583)
      | ~ l1_pre_topc(A_583)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_36,c_7146])).

tff(c_20645,plain,(
    ! [B_35] :
      ( m1_subset_1(u1_struct_0(B_35),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_35,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20619,c_7157])).

tff(c_20721,plain,(
    ! [B_1143] :
      ( m1_subset_1(u1_struct_0(B_1143),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1143,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20645])).

tff(c_34,plain,(
    ! [A_30,B_32] :
      ( k2_pre_topc(A_30,B_32) = k2_struct_0(A_30)
      | ~ v1_tops_1(B_32,A_30)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_20768,plain,(
    ! [B_1143] :
      ( k2_pre_topc('#skF_3',u1_struct_0(B_1143)) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(u1_struct_0(B_1143),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_1143,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20721,c_34])).

tff(c_21102,plain,(
    ! [B_1151] :
      ( k2_pre_topc('#skF_3',u1_struct_0(B_1151)) = k2_struct_0('#skF_3')
      | ~ v1_tops_1(u1_struct_0(B_1151),'#skF_3')
      | ~ m1_pre_topc(B_1151,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20768])).

tff(c_21148,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_7069,c_21102])).

tff(c_21180,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = k2_struct_0('#skF_3')
    | k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20619,c_21148])).

tff(c_21181,plain,(
    k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) != u1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_21180])).

tff(c_20165,plain,(
    ! [A_33] :
      ( '#skF_1'(A_33,u1_struct_0(A_33)) = u1_struct_0(A_33)
      | ~ v3_tdlat_3(A_33)
      | ~ v2_pre_topc(A_33)
      | ~ v1_tdlat_3(A_33)
      | v2_struct_0(A_33)
      | ~ m1_pre_topc(A_33,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_7672,c_20150])).

tff(c_56,plain,(
    ! [A_56,B_60] :
      ( v3_tex_2('#skF_1'(A_56,B_60),A_56)
      | ~ v2_tex_2(B_60,A_56)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v3_tdlat_3(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_20749,plain,(
    ! [B_1143] :
      ( v3_tex_2('#skF_1'('#skF_3',u1_struct_0(B_1143)),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1143),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1143,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20721,c_56])).

tff(c_20806,plain,(
    ! [B_1143] :
      ( v3_tex_2('#skF_1'('#skF_3',u1_struct_0(B_1143)),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1143),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1143,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_6875,c_124,c_20749])).

tff(c_21195,plain,(
    ! [B_1152] :
      ( v3_tex_2('#skF_1'('#skF_3',u1_struct_0(B_1152)),'#skF_3')
      | ~ v2_tex_2(u1_struct_0(B_1152),'#skF_3')
      | ~ m1_pre_topc(B_1152,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_20806])).

tff(c_21207,plain,
    ( v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20165,c_21195])).

tff(c_21231,plain,
    ( v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20619,c_6876,c_169,c_6875,c_20619,c_21207])).

tff(c_21232,plain,
    ( v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_21231])).

tff(c_21234,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_21232])).

tff(c_21237,plain,
    ( ~ v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_7672,c_21234])).

tff(c_21240,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20619,c_6876,c_21237])).

tff(c_21242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_21240])).

tff(c_21243,plain,(
    v3_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_21232])).

tff(c_54,plain,(
    ! [B_55,A_53] :
      ( v1_tops_1(B_55,A_53)
      | ~ v3_tex_2(B_55,A_53)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v3_tdlat_3(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_20754,plain,(
    ! [B_1143] :
      ( v1_tops_1(u1_struct_0(B_1143),'#skF_3')
      | ~ v3_tex_2(u1_struct_0(B_1143),'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1143,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20721,c_54])).

tff(c_20814,plain,(
    ! [B_1143] :
      ( v1_tops_1(u1_struct_0(B_1143),'#skF_3')
      | ~ v3_tex_2(u1_struct_0(B_1143),'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_1143,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_6875,c_124,c_20754])).

tff(c_20815,plain,(
    ! [B_1143] :
      ( v1_tops_1(u1_struct_0(B_1143),'#skF_3')
      | ~ v3_tex_2(u1_struct_0(B_1143),'#skF_3')
      | ~ m1_pre_topc(B_1143,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_20814])).

tff(c_21247,plain,
    ( v1_tops_1(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_21243,c_20815])).

tff(c_21271,plain,(
    v1_tops_1(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20619,c_21247])).

tff(c_7075,plain,(
    ! [A_575,B_576] :
      ( k2_pre_topc(A_575,B_576) = u1_struct_0(A_575)
      | ~ v1_tops_1(B_576,A_575)
      | ~ m1_subset_1(B_576,k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ l1_pre_topc(A_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_7090,plain,(
    ! [A_33,B_35] :
      ( k2_pre_topc(A_33,u1_struct_0(B_35)) = u1_struct_0(A_33)
      | ~ v1_tops_1(u1_struct_0(B_35),A_33)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_36,c_7075])).

tff(c_21362,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_21271,c_7090])).

tff(c_21419,plain,(
    k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20619,c_21362])).

tff(c_21421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21181,c_21419])).

tff(c_21422,plain,(
    k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = k2_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_21180])).

tff(c_7003,plain,(
    ! [B_567,A_568] :
      ( v1_tops_1(B_567,A_568)
      | k2_pre_topc(A_568,B_567) != k2_struct_0(A_568)
      | ~ m1_subset_1(B_567,k1_zfmisc_1(u1_struct_0(A_568)))
      | ~ l1_pre_topc(A_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8372,plain,(
    ! [B_654,A_655] :
      ( v1_tops_1(u1_struct_0(B_654),A_655)
      | k2_pre_topc(A_655,u1_struct_0(B_654)) != k2_struct_0(A_655)
      | ~ m1_pre_topc(B_654,A_655)
      | ~ l1_pre_topc(A_655) ) ),
    inference(resolution,[status(thm)],[c_36,c_7003])).

tff(c_8399,plain,(
    ! [A_655,B_654] :
      ( k2_pre_topc(A_655,u1_struct_0(B_654)) = u1_struct_0(A_655)
      | k2_pre_topc(A_655,u1_struct_0(B_654)) != k2_struct_0(A_655)
      | ~ m1_pre_topc(B_654,A_655)
      | ~ l1_pre_topc(A_655) ) ),
    inference(resolution,[status(thm)],[c_8372,c_7090])).

tff(c_21454,plain,
    ( k2_pre_topc('#skF_3',u1_struct_0('#skF_3')) = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21422,c_8399])).

tff(c_21494,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_20619,c_21422,c_21454])).

tff(c_66,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_70,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_95,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70])).

tff(c_170,plain,(
    ! [A_142,B_143] :
      ( k6_domain_1(A_142,B_143) = k1_tarski(B_143)
      | ~ m1_subset_1(B_143,A_142)
      | v1_xboole_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_186,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_95,c_170])).

tff(c_6784,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_21584,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21494,c_6784])).

tff(c_24,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k2_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22538,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_21584,c_24])).

tff(c_22541,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_22538])).

tff(c_22544,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_22541])).

tff(c_22548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_22544])).

tff(c_22549,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_246,plain,(
    ! [B_157,A_158] :
      ( v1_tdlat_3(B_157)
      | ~ v4_tex_2(B_157,A_158)
      | v2_struct_0(B_157)
      | ~ m1_pre_topc(B_157,A_158)
      | ~ l1_pre_topc(A_158)
      | v2_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_249,plain,
    ( v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_84,c_246])).

tff(c_252,plain,
    ( v1_tdlat_3('#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_82,c_249])).

tff(c_253,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_86,c_252])).

tff(c_448,plain,(
    ! [C_195,A_196,B_197] :
      ( m1_subset_1(C_195,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ m1_subset_1(C_195,k1_zfmisc_1(u1_struct_0(B_197)))
      | ~ m1_pre_topc(B_197,A_196)
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_475,plain,(
    ! [A_200,A_201,B_202] :
      ( m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ m1_pre_topc(B_202,A_201)
      | ~ l1_pre_topc(A_201)
      | ~ r1_tarski(A_200,u1_struct_0(B_202)) ) ),
    inference(resolution,[status(thm)],[c_14,c_448])).

tff(c_479,plain,(
    ! [A_200] :
      ( m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_82,c_475])).

tff(c_483,plain,(
    ! [A_200] :
      ( m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_479])).

tff(c_696,plain,(
    ! [B_217,A_218] :
      ( v2_tex_2(u1_struct_0(B_217),A_218)
      | ~ v1_tdlat_3(B_217)
      | ~ m1_subset_1(u1_struct_0(B_217),k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ m1_pre_topc(B_217,A_218)
      | v2_struct_0(B_217)
      | ~ l1_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_700,plain,(
    ! [B_217] :
      ( v2_tex_2(u1_struct_0(B_217),'#skF_2')
      | ~ v1_tdlat_3(B_217)
      | ~ m1_pre_topc(B_217,'#skF_2')
      | v2_struct_0(B_217)
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(u1_struct_0(B_217),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_483,c_696])).

tff(c_709,plain,(
    ! [B_217] :
      ( v2_tex_2(u1_struct_0(B_217),'#skF_2')
      | ~ v1_tdlat_3(B_217)
      | ~ m1_pre_topc(B_217,'#skF_2')
      | v2_struct_0(B_217)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(u1_struct_0(B_217),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_700])).

tff(c_734,plain,(
    ! [B_220] :
      ( v2_tex_2(u1_struct_0(B_220),'#skF_2')
      | ~ v1_tdlat_3(B_220)
      | ~ m1_pre_topc(B_220,'#skF_2')
      | v2_struct_0(B_220)
      | ~ r1_tarski(u1_struct_0(B_220),u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_709])).

tff(c_742,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_2')
    | ~ v1_tdlat_3('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_734])).

tff(c_748,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'),'#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_253,c_742])).

tff(c_749,plain,(
    v2_tex_2(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_748])).

tff(c_711,plain,(
    ! [B_35,A_33] :
      ( v2_tex_2(u1_struct_0(B_35),A_33)
      | ~ v1_tdlat_3(B_35)
      | v2_struct_0(B_35)
      | v2_struct_0(A_33)
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_36,c_696])).

tff(c_90,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_781,plain,(
    ! [B_223,A_224] :
      ( r1_tarski(B_223,'#skF_1'(A_224,B_223))
      | ~ v2_tex_2(B_223,A_224)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_224)))
      | ~ l1_pre_topc(A_224)
      | ~ v3_tdlat_3(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_2654,plain,(
    ! [A_345,A_346] :
      ( r1_tarski(A_345,'#skF_1'(A_346,A_345))
      | ~ v2_tex_2(A_345,A_346)
      | ~ l1_pre_topc(A_346)
      | ~ v3_tdlat_3(A_346)
      | ~ v2_pre_topc(A_346)
      | v2_struct_0(A_346)
      | ~ r1_tarski(A_345,u1_struct_0(A_346)) ) ),
    inference(resolution,[status(thm)],[c_14,c_781])).

tff(c_2687,plain,(
    ! [A_347] :
      ( r1_tarski(u1_struct_0(A_347),'#skF_1'(A_347,u1_struct_0(A_347)))
      | ~ v2_tex_2(u1_struct_0(A_347),A_347)
      | ~ l1_pre_topc(A_347)
      | ~ v3_tdlat_3(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(resolution,[status(thm)],[c_6,c_2654])).

tff(c_484,plain,(
    ! [A_203] :
      ( m1_subset_1(A_203,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_203,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_479])).

tff(c_529,plain,(
    ! [A_206] :
      ( r1_tarski(A_206,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_206,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_484,c_12])).

tff(c_560,plain,(
    ! [A_206] :
      ( u1_struct_0('#skF_2') = A_206
      | ~ r1_tarski(u1_struct_0('#skF_2'),A_206)
      | ~ r1_tarski(A_206,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_529,c_2])).

tff(c_2690,plain,
    ( '#skF_1'('#skF_2',u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ r1_tarski('#skF_1'('#skF_2',u1_struct_0('#skF_2')),u1_struct_0('#skF_3'))
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v3_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2687,c_560])).

tff(c_2697,plain,
    ( '#skF_1'('#skF_2',u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ r1_tarski('#skF_1'('#skF_2',u1_struct_0('#skF_2')),u1_struct_0('#skF_3'))
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_2690])).

tff(c_2698,plain,
    ( '#skF_1'('#skF_2',u1_struct_0('#skF_2')) = u1_struct_0('#skF_2')
    | ~ r1_tarski('#skF_1'('#skF_2',u1_struct_0('#skF_2')),u1_struct_0('#skF_3'))
    | ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2697])).

tff(c_2701,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2698])).

tff(c_2704,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_711,c_2701])).

tff(c_2710,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2704])).

tff(c_2711,plain,
    ( ~ v1_tdlat_3('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2710])).

tff(c_2714,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2711])).

tff(c_2717,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_2714])).

tff(c_2721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2717])).

tff(c_2723,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2711])).

tff(c_26,plain,(
    ! [C_25,A_19,B_23] :
      ( m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(B_23)))
      | ~ m1_pre_topc(B_23,A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_510,plain,(
    ! [A_203,A_19] :
      ( m1_subset_1(A_203,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_pre_topc('#skF_2',A_19)
      | ~ l1_pre_topc(A_19)
      | ~ r1_tarski(A_203,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_484,c_26])).

tff(c_1022,plain,(
    ! [A_234,B_235] :
      ( v3_tex_2('#skF_1'(A_234,B_235),A_234)
      | ~ v2_tex_2(B_235,A_234)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ l1_pre_topc(A_234)
      | ~ v3_tdlat_3(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_1026,plain,(
    ! [A_200] :
      ( v3_tex_2('#skF_1'('#skF_2',A_200),'#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_483,c_1022])).

tff(c_1038,plain,(
    ! [A_200] :
      ( v3_tex_2('#skF_1'('#skF_2',A_200),'#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_1026])).

tff(c_1039,plain,(
    ! [A_200] :
      ( v3_tex_2('#skF_1'('#skF_2',A_200),'#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1038])).

tff(c_1432,plain,(
    ! [A_260,B_261] :
      ( m1_subset_1('#skF_1'(A_260,B_261),k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ v2_tex_2(B_261,A_260)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_pre_topc(A_260)
      | ~ v3_tdlat_3(A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_5095,plain,(
    ! [A_466,B_467] :
      ( v1_tops_1('#skF_1'(A_466,B_467),A_466)
      | ~ v3_tex_2('#skF_1'(A_466,B_467),A_466)
      | ~ v2_tex_2(B_467,A_466)
      | ~ m1_subset_1(B_467,k1_zfmisc_1(u1_struct_0(A_466)))
      | ~ l1_pre_topc(A_466)
      | ~ v3_tdlat_3(A_466)
      | ~ v2_pre_topc(A_466)
      | v2_struct_0(A_466) ) ),
    inference(resolution,[status(thm)],[c_1432,c_54])).

tff(c_5105,plain,(
    ! [A_200] :
      ( v1_tops_1('#skF_1'('#skF_2',A_200),'#skF_2')
      | ~ m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1039,c_5095])).

tff(c_5118,plain,(
    ! [A_200] :
      ( v1_tops_1('#skF_1'('#skF_2',A_200),'#skF_2')
      | ~ m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_5105])).

tff(c_5120,plain,(
    ! [A_468] :
      ( v1_tops_1('#skF_1'('#skF_2',A_468),'#skF_2')
      | ~ m1_subset_1(A_468,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v2_tex_2(A_468,'#skF_2')
      | ~ r1_tarski(A_468,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5118])).

tff(c_5180,plain,(
    ! [A_200] :
      ( v1_tops_1('#skF_1'('#skF_2',A_200),'#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_483,c_5120])).

tff(c_5686,plain,(
    ! [A_512,B_513] :
      ( k2_pre_topc(A_512,'#skF_1'(A_512,B_513)) = u1_struct_0(A_512)
      | ~ v1_tops_1('#skF_1'(A_512,B_513),A_512)
      | ~ v2_tex_2(B_513,A_512)
      | ~ m1_subset_1(B_513,k1_zfmisc_1(u1_struct_0(A_512)))
      | ~ l1_pre_topc(A_512)
      | ~ v3_tdlat_3(A_512)
      | ~ v2_pre_topc(A_512)
      | v2_struct_0(A_512) ) ),
    inference(resolution,[status(thm)],[c_1432,c_48])).

tff(c_5692,plain,(
    ! [A_200] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_200)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5180,c_5686])).

tff(c_5703,plain,(
    ! [A_200] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_200)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_5692])).

tff(c_5705,plain,(
    ! [A_514] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_514)) = u1_struct_0('#skF_2')
      | ~ m1_subset_1(A_514,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v2_tex_2(A_514,'#skF_2')
      | ~ r1_tarski(A_514,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5703])).

tff(c_5735,plain,(
    ! [A_203] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_203)) = u1_struct_0('#skF_2')
      | ~ v2_tex_2(A_203,'#skF_2')
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_203,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_510,c_5705])).

tff(c_5779,plain,(
    ! [A_515] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_515)) = u1_struct_0('#skF_2')
      | ~ v2_tex_2(A_515,'#skF_2')
      | ~ r1_tarski(A_515,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2723,c_5735])).

tff(c_5815,plain,
    ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',u1_struct_0('#skF_3'))) = u1_struct_0('#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_5779])).

tff(c_5842,plain,(
    k2_pre_topc('#skF_2','#skF_1'('#skF_2',u1_struct_0('#skF_3'))) = u1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_5815])).

tff(c_5912,plain,(
    ! [A_518,B_519] :
      ( k2_pre_topc(A_518,'#skF_1'(A_518,B_519)) = k2_struct_0(A_518)
      | ~ v1_tops_1('#skF_1'(A_518,B_519),A_518)
      | ~ v2_tex_2(B_519,A_518)
      | ~ m1_subset_1(B_519,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ l1_pre_topc(A_518)
      | ~ v3_tdlat_3(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518) ) ),
    inference(resolution,[status(thm)],[c_1432,c_34])).

tff(c_5918,plain,(
    ! [A_200] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_200)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5180,c_5912])).

tff(c_5929,plain,(
    ! [A_200] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_200)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(A_200,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2')
      | ~ v2_tex_2(A_200,'#skF_2')
      | ~ r1_tarski(A_200,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_5918])).

tff(c_5931,plain,(
    ! [A_520] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_520)) = k2_struct_0('#skF_2')
      | ~ m1_subset_1(A_520,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v2_tex_2(A_520,'#skF_2')
      | ~ r1_tarski(A_520,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_5929])).

tff(c_5961,plain,(
    ! [A_203] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_203)) = k2_struct_0('#skF_2')
      | ~ v2_tex_2(A_203,'#skF_2')
      | ~ m1_pre_topc('#skF_2','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_203,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_510,c_5931])).

tff(c_6005,plain,(
    ! [A_521] :
      ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',A_521)) = k2_struct_0('#skF_2')
      | ~ v2_tex_2(A_521,'#skF_2')
      | ~ r1_tarski(A_521,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2723,c_5961])).

tff(c_6041,plain,
    ( k2_pre_topc('#skF_2','#skF_1'('#skF_2',u1_struct_0('#skF_3'))) = k2_struct_0('#skF_2')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_6005])).

tff(c_6068,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_5842,c_6041])).

tff(c_68,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_185,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_170])).

tff(c_187,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_6120,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6068,c_187])).

tff(c_6734,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6120,c_24])).

tff(c_6737,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_6734])).

tff(c_6740,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_6737])).

tff(c_6744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_6740])).

tff(c_6745,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_64,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_96,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k6_domain_1(u1_struct_0('#skF_2'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64])).

tff(c_6783,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k6_domain_1(u1_struct_0('#skF_3'),'#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6745,c_96])).

tff(c_22551,plain,(
    k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) != k2_pre_topc('#skF_2',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22549,c_6783])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_78,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_76,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_72,plain,(
    v3_borsuk_1('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_22550,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k6_domain_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22555,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22549,c_28])).

tff(c_22559,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_22555])).

tff(c_22560,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_22550,c_22559])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_6746,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_6762,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6745,c_28])).

tff(c_6766,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6762])).

tff(c_6767,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6746,c_6766])).

tff(c_24056,plain,(
    ! [A_1249,B_1250,C_1251,E_1252] :
      ( k8_relset_1(u1_struct_0(A_1249),u1_struct_0(B_1250),C_1251,E_1252) = k2_pre_topc(A_1249,E_1252)
      | ~ m1_subset_1(E_1252,k1_zfmisc_1(u1_struct_0(A_1249)))
      | ~ m1_subset_1(E_1252,k1_zfmisc_1(u1_struct_0(B_1250)))
      | ~ v3_borsuk_1(C_1251,A_1249,B_1250)
      | ~ m1_subset_1(C_1251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1249),u1_struct_0(B_1250))))
      | ~ v5_pre_topc(C_1251,A_1249,B_1250)
      | ~ v1_funct_2(C_1251,u1_struct_0(A_1249),u1_struct_0(B_1250))
      | ~ v1_funct_1(C_1251)
      | ~ m1_pre_topc(B_1250,A_1249)
      | ~ v4_tex_2(B_1250,A_1249)
      | v2_struct_0(B_1250)
      | ~ l1_pre_topc(A_1249)
      | ~ v3_tdlat_3(A_1249)
      | ~ v2_pre_topc(A_1249)
      | v2_struct_0(A_1249) ) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_24072,plain,(
    ! [B_1250,C_1251] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_1250),C_1251,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_1250)))
      | ~ v3_borsuk_1(C_1251,'#skF_2',B_1250)
      | ~ m1_subset_1(C_1251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_1250))))
      | ~ v5_pre_topc(C_1251,'#skF_2',B_1250)
      | ~ v1_funct_2(C_1251,u1_struct_0('#skF_2'),u1_struct_0(B_1250))
      | ~ v1_funct_1(C_1251)
      | ~ m1_pre_topc(B_1250,'#skF_2')
      | ~ v4_tex_2(B_1250,'#skF_2')
      | v2_struct_0(B_1250)
      | ~ l1_pre_topc('#skF_2')
      | ~ v3_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6767,c_24056])).

tff(c_24094,plain,(
    ! [B_1250,C_1251] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_1250),C_1251,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_1250)))
      | ~ v3_borsuk_1(C_1251,'#skF_2',B_1250)
      | ~ m1_subset_1(C_1251,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_1250))))
      | ~ v5_pre_topc(C_1251,'#skF_2',B_1250)
      | ~ v1_funct_2(C_1251,u1_struct_0('#skF_2'),u1_struct_0(B_1250))
      | ~ v1_funct_1(C_1251)
      | ~ m1_pre_topc(B_1250,'#skF_2')
      | ~ v4_tex_2(B_1250,'#skF_2')
      | v2_struct_0(B_1250)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_24072])).

tff(c_24204,plain,(
    ! [B_1265,C_1266] :
      ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0(B_1265),C_1266,k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
      | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(B_1265)))
      | ~ v3_borsuk_1(C_1266,'#skF_2',B_1265)
      | ~ m1_subset_1(C_1266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_1265))))
      | ~ v5_pre_topc(C_1266,'#skF_2',B_1265)
      | ~ v1_funct_2(C_1266,u1_struct_0('#skF_2'),u1_struct_0(B_1265))
      | ~ v1_funct_1(C_1266)
      | ~ m1_pre_topc(B_1265,'#skF_2')
      | ~ v4_tex_2(B_1265,'#skF_2')
      | v2_struct_0(B_1265) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_24094])).

tff(c_24215,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | ~ m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ v3_borsuk_1('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_24204])).

tff(c_24220,plain,
    ( k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',k1_tarski('#skF_6')) = k2_pre_topc('#skF_2',k1_tarski('#skF_6'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_72,c_22560,c_24215])).

tff(c_24222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_22551,c_24220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.80/5.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.80/5.52  
% 12.80/5.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.80/5.53  %$ v5_pre_topc > v3_borsuk_1 > v1_funct_2 > v4_tex_2 > v3_tex_2 > v2_tex_2 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k6_domain_1 > k2_zfmisc_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.80/5.53  
% 12.80/5.53  %Foreground sorts:
% 12.80/5.53  
% 12.80/5.53  
% 12.80/5.53  %Background operators:
% 12.80/5.53  
% 12.80/5.53  
% 12.80/5.53  %Foreground operators:
% 12.80/5.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.80/5.53  tff(v3_borsuk_1, type, v3_borsuk_1: ($i * $i * $i) > $o).
% 12.80/5.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.80/5.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.80/5.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.80/5.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.80/5.53  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 12.80/5.53  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 12.80/5.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.80/5.53  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 12.80/5.53  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 12.80/5.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.80/5.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.80/5.53  tff('#skF_5', type, '#skF_5': $i).
% 12.80/5.53  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 12.80/5.53  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 12.80/5.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.80/5.53  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 12.80/5.53  tff('#skF_6', type, '#skF_6': $i).
% 12.80/5.53  tff('#skF_2', type, '#skF_2': $i).
% 12.80/5.53  tff('#skF_3', type, '#skF_3': $i).
% 12.80/5.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.80/5.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.80/5.53  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 12.80/5.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.80/5.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.80/5.53  tff('#skF_4', type, '#skF_4': $i).
% 12.80/5.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.80/5.53  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 12.80/5.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.80/5.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.80/5.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.80/5.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.80/5.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.80/5.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.80/5.53  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.80/5.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.80/5.53  
% 13.16/5.56  tff(f_297, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k6_domain_1(u1_struct_0(B), D)) = k2_pre_topc(A, k6_domain_1(u1_struct_0(A), E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tex_2)).
% 13.16/5.56  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 13.16/5.56  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 13.16/5.56  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 13.16/5.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.16/5.56  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.16/5.56  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 13.16/5.56  tff(f_161, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 13.16/5.56  tff(f_134, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v1_tdlat_3(B) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc18_tex_2)).
% 13.16/5.56  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & v4_tex_2(B, A)) => (~v2_struct_0(B) & v1_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc35_tex_2)).
% 13.16/5.56  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 13.16/5.56  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 13.16/5.56  tff(f_181, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 13.16/5.56  tff(f_220, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 13.16/5.56  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 13.16/5.56  tff(f_197, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tex_2)).
% 13.16/5.56  tff(f_102, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 13.16/5.56  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 13.16/5.56  tff(f_95, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 13.16/5.56  tff(f_258, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v4_tex_2(B, A)) & m1_pre_topc(B, A)) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v3_borsuk_1(C, A, B) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((D = E) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D) = k2_pre_topc(A, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tex_2)).
% 13.16/5.56  tff(c_86, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_88, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_82, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_114, plain, (![B_123, A_124]: (l1_pre_topc(B_123) | ~m1_pre_topc(B_123, A_124) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.16/5.56  tff(c_120, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_82, c_114])).
% 13.16/5.56  tff(c_124, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_120])).
% 13.16/5.56  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.16/5.56  tff(c_38, plain, (![A_36]: (m1_pre_topc(A_36, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_122])).
% 13.16/5.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.16/5.56  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.16/5.56  tff(c_7146, plain, (![C_582, A_583, B_584]: (m1_subset_1(C_582, k1_zfmisc_1(u1_struct_0(A_583))) | ~m1_subset_1(C_582, k1_zfmisc_1(u1_struct_0(B_584))) | ~m1_pre_topc(B_584, A_583) | ~l1_pre_topc(A_583))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.16/5.56  tff(c_7258, plain, (![A_591, A_592, B_593]: (m1_subset_1(A_591, k1_zfmisc_1(u1_struct_0(A_592))) | ~m1_pre_topc(B_593, A_592) | ~l1_pre_topc(A_592) | ~r1_tarski(A_591, u1_struct_0(B_593)))), inference(resolution, [status(thm)], [c_14, c_7146])).
% 13.16/5.56  tff(c_7262, plain, (![A_591]: (m1_subset_1(A_591, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_591, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_82, c_7258])).
% 13.16/5.56  tff(c_7267, plain, (![A_594]: (m1_subset_1(A_594, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_594, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7262])).
% 13.16/5.56  tff(c_46, plain, (![B_45, A_43]: (v1_tops_1(B_45, A_43) | k2_pre_topc(A_43, B_45)!=u1_struct_0(A_43) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_161])).
% 13.16/5.56  tff(c_7281, plain, (![A_594]: (v1_tops_1(A_594, '#skF_2') | k2_pre_topc('#skF_2', A_594)!=u1_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_594, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_7267, c_46])).
% 13.16/5.56  tff(c_7422, plain, (![A_601]: (v1_tops_1(A_601, '#skF_2') | k2_pre_topc('#skF_2', A_601)!=u1_struct_0('#skF_2') | ~r1_tarski(A_601, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7281])).
% 13.16/5.56  tff(c_7448, plain, (v1_tops_1(u1_struct_0('#skF_3'), '#skF_2') | k2_pre_topc('#skF_2', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6, c_7422])).
% 13.16/5.56  tff(c_7471, plain, (k2_pre_topc('#skF_2', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_7448])).
% 13.16/5.56  tff(c_48, plain, (![A_43, B_45]: (k2_pre_topc(A_43, B_45)=u1_struct_0(A_43) | ~v1_tops_1(B_45, A_43) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_161])).
% 13.16/5.56  tff(c_7275, plain, (![A_594]: (k2_pre_topc('#skF_2', A_594)=u1_struct_0('#skF_2') | ~v1_tops_1(A_594, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_594, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_7267, c_48])).
% 13.16/5.56  tff(c_7601, plain, (![A_609]: (k2_pre_topc('#skF_2', A_609)=u1_struct_0('#skF_2') | ~v1_tops_1(A_609, '#skF_2') | ~r1_tarski(A_609, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7275])).
% 13.16/5.56  tff(c_7617, plain, (k2_pre_topc('#skF_2', u1_struct_0('#skF_3'))=u1_struct_0('#skF_2') | ~v1_tops_1(u1_struct_0('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_7601])).
% 13.16/5.56  tff(c_7629, plain, (~v1_tops_1(u1_struct_0('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_7471, c_7617])).
% 13.16/5.56  tff(c_94, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_6828, plain, (![B_533, A_534]: (v3_tdlat_3(B_533) | ~v1_tdlat_3(B_533) | ~m1_pre_topc(B_533, A_534) | ~l1_pre_topc(A_534) | v2_struct_0(A_534))), inference(cnfTransformation, [status(thm)], [f_134])).
% 13.16/5.56  tff(c_6834, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_6828])).
% 13.16/5.56  tff(c_6838, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_6834])).
% 13.16/5.56  tff(c_6839, plain, (v3_tdlat_3('#skF_3') | ~v1_tdlat_3('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_94, c_6838])).
% 13.16/5.56  tff(c_6840, plain, (~v1_tdlat_3('#skF_3')), inference(splitLeft, [status(thm)], [c_6839])).
% 13.16/5.56  tff(c_84, plain, (v4_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_6866, plain, (![B_543, A_544]: (v1_tdlat_3(B_543) | ~v4_tex_2(B_543, A_544) | v2_struct_0(B_543) | ~m1_pre_topc(B_543, A_544) | ~l1_pre_topc(A_544) | v2_struct_0(A_544))), inference(cnfTransformation, [status(thm)], [f_152])).
% 13.16/5.56  tff(c_6869, plain, (v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_6866])).
% 13.16/5.56  tff(c_6872, plain, (v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_6869])).
% 13.16/5.56  tff(c_6874, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_86, c_6840, c_6872])).
% 13.16/5.56  tff(c_6876, plain, (v1_tdlat_3('#skF_3')), inference(splitRight, [status(thm)], [c_6839])).
% 13.16/5.56  tff(c_92, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_159, plain, (![B_140, A_141]: (v2_pre_topc(B_140) | ~m1_pre_topc(B_140, A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.16/5.56  tff(c_165, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_82, c_159])).
% 13.16/5.56  tff(c_169, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_165])).
% 13.16/5.56  tff(c_6875, plain, (v3_tdlat_3('#skF_3')), inference(splitRight, [status(thm)], [c_6839])).
% 13.16/5.56  tff(c_36, plain, (![B_35, A_33]: (m1_subset_1(u1_struct_0(B_35), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.16/5.56  tff(c_7657, plain, (![B_611, A_612]: (v2_tex_2(u1_struct_0(B_611), A_612) | ~v1_tdlat_3(B_611) | ~m1_subset_1(u1_struct_0(B_611), k1_zfmisc_1(u1_struct_0(A_612))) | ~m1_pre_topc(B_611, A_612) | v2_struct_0(B_611) | ~l1_pre_topc(A_612) | v2_struct_0(A_612))), inference(cnfTransformation, [status(thm)], [f_181])).
% 13.16/5.56  tff(c_7672, plain, (![B_35, A_33]: (v2_tex_2(u1_struct_0(B_35), A_33) | ~v1_tdlat_3(B_35) | v2_struct_0(B_35) | v2_struct_0(A_33) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_36, c_7657])).
% 13.16/5.56  tff(c_7394, plain, (![B_599, A_600]: (r1_tarski(B_599, '#skF_1'(A_600, B_599)) | ~v2_tex_2(B_599, A_600) | ~m1_subset_1(B_599, k1_zfmisc_1(u1_struct_0(A_600))) | ~l1_pre_topc(A_600) | ~v3_tdlat_3(A_600) | ~v2_pre_topc(A_600) | v2_struct_0(A_600))), inference(cnfTransformation, [status(thm)], [f_220])).
% 13.16/5.56  tff(c_9760, plain, (![A_758, A_759]: (r1_tarski(A_758, '#skF_1'(A_759, A_758)) | ~v2_tex_2(A_758, A_759) | ~l1_pre_topc(A_759) | ~v3_tdlat_3(A_759) | ~v2_pre_topc(A_759) | v2_struct_0(A_759) | ~r1_tarski(A_758, u1_struct_0(A_759)))), inference(resolution, [status(thm)], [c_14, c_7394])).
% 13.16/5.56  tff(c_9801, plain, (![A_759]: (r1_tarski(u1_struct_0(A_759), '#skF_1'(A_759, u1_struct_0(A_759))) | ~v2_tex_2(u1_struct_0(A_759), A_759) | ~l1_pre_topc(A_759) | ~v3_tdlat_3(A_759) | ~v2_pre_topc(A_759) | v2_struct_0(A_759))), inference(resolution, [status(thm)], [c_6, c_9760])).
% 13.16/5.56  tff(c_8197, plain, (![A_640, B_641]: (m1_subset_1('#skF_1'(A_640, B_641), k1_zfmisc_1(u1_struct_0(A_640))) | ~v2_tex_2(B_641, A_640) | ~m1_subset_1(B_641, k1_zfmisc_1(u1_struct_0(A_640))) | ~l1_pre_topc(A_640) | ~v3_tdlat_3(A_640) | ~v2_pre_topc(A_640) | v2_struct_0(A_640))), inference(cnfTransformation, [status(thm)], [f_220])).
% 13.16/5.56  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.16/5.56  tff(c_10439, plain, (![A_776, B_777]: (r1_tarski('#skF_1'(A_776, B_777), u1_struct_0(A_776)) | ~v2_tex_2(B_777, A_776) | ~m1_subset_1(B_777, k1_zfmisc_1(u1_struct_0(A_776))) | ~l1_pre_topc(A_776) | ~v3_tdlat_3(A_776) | ~v2_pre_topc(A_776) | v2_struct_0(A_776))), inference(resolution, [status(thm)], [c_8197, c_12])).
% 13.16/5.56  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.16/5.56  tff(c_17791, plain, (![A_1071, B_1072]: (u1_struct_0(A_1071)='#skF_1'(A_1071, B_1072) | ~r1_tarski(u1_struct_0(A_1071), '#skF_1'(A_1071, B_1072)) | ~v2_tex_2(B_1072, A_1071) | ~m1_subset_1(B_1072, k1_zfmisc_1(u1_struct_0(A_1071))) | ~l1_pre_topc(A_1071) | ~v3_tdlat_3(A_1071) | ~v2_pre_topc(A_1071) | v2_struct_0(A_1071))), inference(resolution, [status(thm)], [c_10439, c_2])).
% 13.16/5.56  tff(c_20106, plain, (![A_1137]: ('#skF_1'(A_1137, u1_struct_0(A_1137))=u1_struct_0(A_1137) | ~m1_subset_1(u1_struct_0(A_1137), k1_zfmisc_1(u1_struct_0(A_1137))) | ~v2_tex_2(u1_struct_0(A_1137), A_1137) | ~l1_pre_topc(A_1137) | ~v3_tdlat_3(A_1137) | ~v2_pre_topc(A_1137) | v2_struct_0(A_1137))), inference(resolution, [status(thm)], [c_9801, c_17791])).
% 13.16/5.56  tff(c_20135, plain, (![A_1137]: ('#skF_1'(A_1137, u1_struct_0(A_1137))=u1_struct_0(A_1137) | ~v2_tex_2(u1_struct_0(A_1137), A_1137) | ~l1_pre_topc(A_1137) | ~v3_tdlat_3(A_1137) | ~v2_pre_topc(A_1137) | v2_struct_0(A_1137) | ~r1_tarski(u1_struct_0(A_1137), u1_struct_0(A_1137)))), inference(resolution, [status(thm)], [c_14, c_20106])).
% 13.16/5.56  tff(c_20150, plain, (![A_1138]: ('#skF_1'(A_1138, u1_struct_0(A_1138))=u1_struct_0(A_1138) | ~v2_tex_2(u1_struct_0(A_1138), A_1138) | ~l1_pre_topc(A_1138) | ~v3_tdlat_3(A_1138) | ~v2_pre_topc(A_1138) | v2_struct_0(A_1138))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20135])).
% 13.16/5.56  tff(c_20170, plain, (![A_1139]: ('#skF_1'(A_1139, u1_struct_0(A_1139))=u1_struct_0(A_1139) | ~v3_tdlat_3(A_1139) | ~v2_pre_topc(A_1139) | ~v1_tdlat_3(A_1139) | v2_struct_0(A_1139) | ~m1_pre_topc(A_1139, A_1139) | ~l1_pre_topc(A_1139))), inference(resolution, [status(thm)], [c_7672, c_20150])).
% 13.16/5.56  tff(c_32, plain, (![B_32, A_30]: (v1_tops_1(B_32, A_30) | k2_pre_topc(A_30, B_32)!=k2_struct_0(A_30) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.16/5.56  tff(c_7278, plain, (![A_594]: (v1_tops_1(A_594, '#skF_2') | k2_pre_topc('#skF_2', A_594)!=k2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_594, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_7267, c_32])).
% 13.16/5.56  tff(c_7303, plain, (![A_594]: (v1_tops_1(A_594, '#skF_2') | k2_pre_topc('#skF_2', A_594)!=k2_struct_0('#skF_2') | ~r1_tarski(A_594, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_7278])).
% 13.16/5.56  tff(c_10457, plain, (![B_777]: (v1_tops_1('#skF_1'('#skF_3', B_777), '#skF_2') | k2_pre_topc('#skF_2', '#skF_1'('#skF_3', B_777))!=k2_struct_0('#skF_2') | ~v2_tex_2(B_777, '#skF_3') | ~m1_subset_1(B_777, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_10439, c_7303])).
% 13.16/5.56  tff(c_10509, plain, (![B_777]: (v1_tops_1('#skF_1'('#skF_3', B_777), '#skF_2') | k2_pre_topc('#skF_2', '#skF_1'('#skF_3', B_777))!=k2_struct_0('#skF_2') | ~v2_tex_2(B_777, '#skF_3') | ~m1_subset_1(B_777, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_6875, c_124, c_10457])).
% 13.16/5.56  tff(c_11504, plain, (![B_818]: (v1_tops_1('#skF_1'('#skF_3', B_818), '#skF_2') | k2_pre_topc('#skF_2', '#skF_1'('#skF_3', B_818))!=k2_struct_0('#skF_2') | ~v2_tex_2(B_818, '#skF_3') | ~m1_subset_1(B_818, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_86, c_10509])).
% 13.16/5.56  tff(c_11532, plain, (![B_35]: (v1_tops_1('#skF_1'('#skF_3', u1_struct_0(B_35)), '#skF_2') | k2_pre_topc('#skF_2', '#skF_1'('#skF_3', u1_struct_0(B_35)))!=k2_struct_0('#skF_2') | ~v2_tex_2(u1_struct_0(B_35), '#skF_3') | ~m1_pre_topc(B_35, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_11504])).
% 13.16/5.56  tff(c_11562, plain, (![B_35]: (v1_tops_1('#skF_1'('#skF_3', u1_struct_0(B_35)), '#skF_2') | k2_pre_topc('#skF_2', '#skF_1'('#skF_3', u1_struct_0(B_35)))!=k2_struct_0('#skF_2') | ~v2_tex_2(u1_struct_0(B_35), '#skF_3') | ~m1_pre_topc(B_35, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_11532])).
% 13.16/5.56  tff(c_20303, plain, (v1_tops_1(u1_struct_0('#skF_3'), '#skF_2') | k2_pre_topc('#skF_2', '#skF_1'('#skF_3', u1_struct_0('#skF_3')))!=k2_struct_0('#skF_2') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20170, c_11562])).
% 13.16/5.56  tff(c_20493, plain, (v1_tops_1(u1_struct_0('#skF_3'), '#skF_2') | k2_pre_topc('#skF_2', '#skF_1'('#skF_3', u1_struct_0('#skF_3')))!=k2_struct_0('#skF_2') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_6876, c_169, c_6875, c_20303])).
% 13.16/5.56  tff(c_20494, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_3', u1_struct_0('#skF_3')))!=k2_struct_0('#skF_2') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_86, c_7629, c_20493])).
% 13.16/5.56  tff(c_20563, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_20494])).
% 13.16/5.56  tff(c_20613, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_20563])).
% 13.16/5.56  tff(c_20617, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_20613])).
% 13.16/5.56  tff(c_20619, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_20494])).
% 13.16/5.56  tff(c_6980, plain, (![B_565, A_566]: (v1_tops_1(B_565, A_566) | k2_pre_topc(A_566, B_565)!=u1_struct_0(A_566) | ~m1_subset_1(B_565, k1_zfmisc_1(u1_struct_0(A_566))) | ~l1_pre_topc(A_566))), inference(cnfTransformation, [status(thm)], [f_161])).
% 13.16/5.56  tff(c_7048, plain, (![A_572, A_573]: (v1_tops_1(A_572, A_573) | k2_pre_topc(A_573, A_572)!=u1_struct_0(A_573) | ~l1_pre_topc(A_573) | ~r1_tarski(A_572, u1_struct_0(A_573)))), inference(resolution, [status(thm)], [c_14, c_6980])).
% 13.16/5.56  tff(c_7069, plain, (![A_573]: (v1_tops_1(u1_struct_0(A_573), A_573) | k2_pre_topc(A_573, u1_struct_0(A_573))!=u1_struct_0(A_573) | ~l1_pre_topc(A_573))), inference(resolution, [status(thm)], [c_6, c_7048])).
% 13.16/5.56  tff(c_7157, plain, (![B_35, A_583, A_33]: (m1_subset_1(u1_struct_0(B_35), k1_zfmisc_1(u1_struct_0(A_583))) | ~m1_pre_topc(A_33, A_583) | ~l1_pre_topc(A_583) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_36, c_7146])).
% 13.16/5.56  tff(c_20645, plain, (![B_35]: (m1_subset_1(u1_struct_0(B_35), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_35, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_20619, c_7157])).
% 13.16/5.56  tff(c_20721, plain, (![B_1143]: (m1_subset_1(u1_struct_0(B_1143), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(B_1143, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_20645])).
% 13.16/5.56  tff(c_34, plain, (![A_30, B_32]: (k2_pre_topc(A_30, B_32)=k2_struct_0(A_30) | ~v1_tops_1(B_32, A_30) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.16/5.56  tff(c_20768, plain, (![B_1143]: (k2_pre_topc('#skF_3', u1_struct_0(B_1143))=k2_struct_0('#skF_3') | ~v1_tops_1(u1_struct_0(B_1143), '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_1143, '#skF_3'))), inference(resolution, [status(thm)], [c_20721, c_34])).
% 13.16/5.56  tff(c_21102, plain, (![B_1151]: (k2_pre_topc('#skF_3', u1_struct_0(B_1151))=k2_struct_0('#skF_3') | ~v1_tops_1(u1_struct_0(B_1151), '#skF_3') | ~m1_pre_topc(B_1151, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_20768])).
% 13.16/5.56  tff(c_21148, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=k2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_7069, c_21102])).
% 13.16/5.56  tff(c_21180, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=k2_struct_0('#skF_3') | k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_20619, c_21148])).
% 13.16/5.56  tff(c_21181, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))!=u1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_21180])).
% 13.16/5.56  tff(c_20165, plain, (![A_33]: ('#skF_1'(A_33, u1_struct_0(A_33))=u1_struct_0(A_33) | ~v3_tdlat_3(A_33) | ~v2_pre_topc(A_33) | ~v1_tdlat_3(A_33) | v2_struct_0(A_33) | ~m1_pre_topc(A_33, A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_7672, c_20150])).
% 13.16/5.56  tff(c_56, plain, (![A_56, B_60]: (v3_tex_2('#skF_1'(A_56, B_60), A_56) | ~v2_tex_2(B_60, A_56) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56) | ~v3_tdlat_3(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_220])).
% 13.16/5.56  tff(c_20749, plain, (![B_1143]: (v3_tex_2('#skF_1'('#skF_3', u1_struct_0(B_1143)), '#skF_3') | ~v2_tex_2(u1_struct_0(B_1143), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_1143, '#skF_3'))), inference(resolution, [status(thm)], [c_20721, c_56])).
% 13.16/5.56  tff(c_20806, plain, (![B_1143]: (v3_tex_2('#skF_1'('#skF_3', u1_struct_0(B_1143)), '#skF_3') | ~v2_tex_2(u1_struct_0(B_1143), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_1143, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_6875, c_124, c_20749])).
% 13.16/5.56  tff(c_21195, plain, (![B_1152]: (v3_tex_2('#skF_1'('#skF_3', u1_struct_0(B_1152)), '#skF_3') | ~v2_tex_2(u1_struct_0(B_1152), '#skF_3') | ~m1_pre_topc(B_1152, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_86, c_20806])).
% 13.16/5.56  tff(c_21207, plain, (v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20165, c_21195])).
% 13.16/5.56  tff(c_21231, plain, (v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_20619, c_6876, c_169, c_6875, c_20619, c_21207])).
% 13.16/5.56  tff(c_21232, plain, (v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_86, c_21231])).
% 13.16/5.56  tff(c_21234, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_21232])).
% 13.16/5.56  tff(c_21237, plain, (~v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_7672, c_21234])).
% 13.16/5.56  tff(c_21240, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_20619, c_6876, c_21237])).
% 13.16/5.56  tff(c_21242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_21240])).
% 13.16/5.56  tff(c_21243, plain, (v3_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_21232])).
% 13.16/5.56  tff(c_54, plain, (![B_55, A_53]: (v1_tops_1(B_55, A_53) | ~v3_tex_2(B_55, A_53) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v3_tdlat_3(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_197])).
% 13.16/5.56  tff(c_20754, plain, (![B_1143]: (v1_tops_1(u1_struct_0(B_1143), '#skF_3') | ~v3_tex_2(u1_struct_0(B_1143), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_1143, '#skF_3'))), inference(resolution, [status(thm)], [c_20721, c_54])).
% 13.16/5.56  tff(c_20814, plain, (![B_1143]: (v1_tops_1(u1_struct_0(B_1143), '#skF_3') | ~v3_tex_2(u1_struct_0(B_1143), '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_1143, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_6875, c_124, c_20754])).
% 13.16/5.56  tff(c_20815, plain, (![B_1143]: (v1_tops_1(u1_struct_0(B_1143), '#skF_3') | ~v3_tex_2(u1_struct_0(B_1143), '#skF_3') | ~m1_pre_topc(B_1143, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_86, c_20814])).
% 13.16/5.56  tff(c_21247, plain, (v1_tops_1(u1_struct_0('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_21243, c_20815])).
% 13.16/5.56  tff(c_21271, plain, (v1_tops_1(u1_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20619, c_21247])).
% 13.16/5.56  tff(c_7075, plain, (![A_575, B_576]: (k2_pre_topc(A_575, B_576)=u1_struct_0(A_575) | ~v1_tops_1(B_576, A_575) | ~m1_subset_1(B_576, k1_zfmisc_1(u1_struct_0(A_575))) | ~l1_pre_topc(A_575))), inference(cnfTransformation, [status(thm)], [f_161])).
% 13.16/5.56  tff(c_7090, plain, (![A_33, B_35]: (k2_pre_topc(A_33, u1_struct_0(B_35))=u1_struct_0(A_33) | ~v1_tops_1(u1_struct_0(B_35), A_33) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_36, c_7075])).
% 13.16/5.56  tff(c_21362, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_21271, c_7090])).
% 13.16/5.56  tff(c_21419, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_20619, c_21362])).
% 13.16/5.56  tff(c_21421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21181, c_21419])).
% 13.16/5.56  tff(c_21422, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=k2_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_21180])).
% 13.16/5.56  tff(c_7003, plain, (![B_567, A_568]: (v1_tops_1(B_567, A_568) | k2_pre_topc(A_568, B_567)!=k2_struct_0(A_568) | ~m1_subset_1(B_567, k1_zfmisc_1(u1_struct_0(A_568))) | ~l1_pre_topc(A_568))), inference(cnfTransformation, [status(thm)], [f_111])).
% 13.16/5.56  tff(c_8372, plain, (![B_654, A_655]: (v1_tops_1(u1_struct_0(B_654), A_655) | k2_pre_topc(A_655, u1_struct_0(B_654))!=k2_struct_0(A_655) | ~m1_pre_topc(B_654, A_655) | ~l1_pre_topc(A_655))), inference(resolution, [status(thm)], [c_36, c_7003])).
% 13.16/5.56  tff(c_8399, plain, (![A_655, B_654]: (k2_pre_topc(A_655, u1_struct_0(B_654))=u1_struct_0(A_655) | k2_pre_topc(A_655, u1_struct_0(B_654))!=k2_struct_0(A_655) | ~m1_pre_topc(B_654, A_655) | ~l1_pre_topc(A_655))), inference(resolution, [status(thm)], [c_8372, c_7090])).
% 13.16/5.56  tff(c_21454, plain, (k2_pre_topc('#skF_3', u1_struct_0('#skF_3'))=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21422, c_8399])).
% 13.16/5.56  tff(c_21494, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_20619, c_21422, c_21454])).
% 13.16/5.56  tff(c_66, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_70, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_95, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70])).
% 13.16/5.56  tff(c_170, plain, (![A_142, B_143]: (k6_domain_1(A_142, B_143)=k1_tarski(B_143) | ~m1_subset_1(B_143, A_142) | v1_xboole_0(A_142))), inference(cnfTransformation, [status(thm)], [f_102])).
% 13.16/5.56  tff(c_186, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_95, c_170])).
% 13.16/5.56  tff(c_6784, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_186])).
% 13.16/5.56  tff(c_21584, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21494, c_6784])).
% 13.16/5.56  tff(c_24, plain, (![A_18]: (~v1_xboole_0(k2_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.16/5.56  tff(c_22538, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_21584, c_24])).
% 13.16/5.56  tff(c_22541, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_86, c_22538])).
% 13.16/5.56  tff(c_22544, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_22541])).
% 13.16/5.56  tff(c_22548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_22544])).
% 13.16/5.56  tff(c_22549, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_186])).
% 13.16/5.56  tff(c_246, plain, (![B_157, A_158]: (v1_tdlat_3(B_157) | ~v4_tex_2(B_157, A_158) | v2_struct_0(B_157) | ~m1_pre_topc(B_157, A_158) | ~l1_pre_topc(A_158) | v2_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_152])).
% 13.16/5.56  tff(c_249, plain, (v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_84, c_246])).
% 13.16/5.56  tff(c_252, plain, (v1_tdlat_3('#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_82, c_249])).
% 13.16/5.56  tff(c_253, plain, (v1_tdlat_3('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_94, c_86, c_252])).
% 13.16/5.56  tff(c_448, plain, (![C_195, A_196, B_197]: (m1_subset_1(C_195, k1_zfmisc_1(u1_struct_0(A_196))) | ~m1_subset_1(C_195, k1_zfmisc_1(u1_struct_0(B_197))) | ~m1_pre_topc(B_197, A_196) | ~l1_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.16/5.56  tff(c_475, plain, (![A_200, A_201, B_202]: (m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~m1_pre_topc(B_202, A_201) | ~l1_pre_topc(A_201) | ~r1_tarski(A_200, u1_struct_0(B_202)))), inference(resolution, [status(thm)], [c_14, c_448])).
% 13.16/5.56  tff(c_479, plain, (![A_200]: (m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_82, c_475])).
% 13.16/5.56  tff(c_483, plain, (![A_200]: (m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_479])).
% 13.16/5.56  tff(c_696, plain, (![B_217, A_218]: (v2_tex_2(u1_struct_0(B_217), A_218) | ~v1_tdlat_3(B_217) | ~m1_subset_1(u1_struct_0(B_217), k1_zfmisc_1(u1_struct_0(A_218))) | ~m1_pre_topc(B_217, A_218) | v2_struct_0(B_217) | ~l1_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_181])).
% 13.16/5.56  tff(c_700, plain, (![B_217]: (v2_tex_2(u1_struct_0(B_217), '#skF_2') | ~v1_tdlat_3(B_217) | ~m1_pre_topc(B_217, '#skF_2') | v2_struct_0(B_217) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(u1_struct_0(B_217), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_483, c_696])).
% 13.16/5.56  tff(c_709, plain, (![B_217]: (v2_tex_2(u1_struct_0(B_217), '#skF_2') | ~v1_tdlat_3(B_217) | ~m1_pre_topc(B_217, '#skF_2') | v2_struct_0(B_217) | v2_struct_0('#skF_2') | ~r1_tarski(u1_struct_0(B_217), u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_700])).
% 13.16/5.56  tff(c_734, plain, (![B_220]: (v2_tex_2(u1_struct_0(B_220), '#skF_2') | ~v1_tdlat_3(B_220) | ~m1_pre_topc(B_220, '#skF_2') | v2_struct_0(B_220) | ~r1_tarski(u1_struct_0(B_220), u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_709])).
% 13.16/5.56  tff(c_742, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_2') | ~v1_tdlat_3('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_734])).
% 13.16/5.56  tff(c_748, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_253, c_742])).
% 13.16/5.56  tff(c_749, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_86, c_748])).
% 13.16/5.56  tff(c_711, plain, (![B_35, A_33]: (v2_tex_2(u1_struct_0(B_35), A_33) | ~v1_tdlat_3(B_35) | v2_struct_0(B_35) | v2_struct_0(A_33) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_36, c_696])).
% 13.16/5.56  tff(c_90, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_781, plain, (![B_223, A_224]: (r1_tarski(B_223, '#skF_1'(A_224, B_223)) | ~v2_tex_2(B_223, A_224) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_224))) | ~l1_pre_topc(A_224) | ~v3_tdlat_3(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224))), inference(cnfTransformation, [status(thm)], [f_220])).
% 13.16/5.56  tff(c_2654, plain, (![A_345, A_346]: (r1_tarski(A_345, '#skF_1'(A_346, A_345)) | ~v2_tex_2(A_345, A_346) | ~l1_pre_topc(A_346) | ~v3_tdlat_3(A_346) | ~v2_pre_topc(A_346) | v2_struct_0(A_346) | ~r1_tarski(A_345, u1_struct_0(A_346)))), inference(resolution, [status(thm)], [c_14, c_781])).
% 13.16/5.56  tff(c_2687, plain, (![A_347]: (r1_tarski(u1_struct_0(A_347), '#skF_1'(A_347, u1_struct_0(A_347))) | ~v2_tex_2(u1_struct_0(A_347), A_347) | ~l1_pre_topc(A_347) | ~v3_tdlat_3(A_347) | ~v2_pre_topc(A_347) | v2_struct_0(A_347))), inference(resolution, [status(thm)], [c_6, c_2654])).
% 13.16/5.56  tff(c_484, plain, (![A_203]: (m1_subset_1(A_203, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_203, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_479])).
% 13.16/5.56  tff(c_529, plain, (![A_206]: (r1_tarski(A_206, u1_struct_0('#skF_2')) | ~r1_tarski(A_206, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_484, c_12])).
% 13.16/5.56  tff(c_560, plain, (![A_206]: (u1_struct_0('#skF_2')=A_206 | ~r1_tarski(u1_struct_0('#skF_2'), A_206) | ~r1_tarski(A_206, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_529, c_2])).
% 13.16/5.56  tff(c_2690, plain, ('#skF_1'('#skF_2', u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~r1_tarski('#skF_1'('#skF_2', u1_struct_0('#skF_2')), u1_struct_0('#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2687, c_560])).
% 13.16/5.56  tff(c_2697, plain, ('#skF_1'('#skF_2', u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~r1_tarski('#skF_1'('#skF_2', u1_struct_0('#skF_2')), u1_struct_0('#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_2690])).
% 13.16/5.56  tff(c_2698, plain, ('#skF_1'('#skF_2', u1_struct_0('#skF_2'))=u1_struct_0('#skF_2') | ~r1_tarski('#skF_1'('#skF_2', u1_struct_0('#skF_2')), u1_struct_0('#skF_3')) | ~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_94, c_2697])).
% 13.16/5.56  tff(c_2701, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_2698])).
% 13.16/5.56  tff(c_2704, plain, (~v1_tdlat_3('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_711, c_2701])).
% 13.16/5.56  tff(c_2710, plain, (~v1_tdlat_3('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2704])).
% 13.16/5.56  tff(c_2711, plain, (~v1_tdlat_3('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_94, c_2710])).
% 13.16/5.56  tff(c_2714, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_2711])).
% 13.16/5.56  tff(c_2717, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_2714])).
% 13.16/5.56  tff(c_2721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_2717])).
% 13.16/5.56  tff(c_2723, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_2711])).
% 13.16/5.56  tff(c_26, plain, (![C_25, A_19, B_23]: (m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(B_23))) | ~m1_pre_topc(B_23, A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.16/5.56  tff(c_510, plain, (![A_203, A_19]: (m1_subset_1(A_203, k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_pre_topc('#skF_2', A_19) | ~l1_pre_topc(A_19) | ~r1_tarski(A_203, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_484, c_26])).
% 13.16/5.56  tff(c_1022, plain, (![A_234, B_235]: (v3_tex_2('#skF_1'(A_234, B_235), A_234) | ~v2_tex_2(B_235, A_234) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_234))) | ~l1_pre_topc(A_234) | ~v3_tdlat_3(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(cnfTransformation, [status(thm)], [f_220])).
% 13.16/5.56  tff(c_1026, plain, (![A_200]: (v3_tex_2('#skF_1'('#skF_2', A_200), '#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_483, c_1022])).
% 13.16/5.56  tff(c_1038, plain, (![A_200]: (v3_tex_2('#skF_1'('#skF_2', A_200), '#skF_2') | ~v2_tex_2(A_200, '#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_1026])).
% 13.16/5.56  tff(c_1039, plain, (![A_200]: (v3_tex_2('#skF_1'('#skF_2', A_200), '#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_1038])).
% 13.16/5.56  tff(c_1432, plain, (![A_260, B_261]: (m1_subset_1('#skF_1'(A_260, B_261), k1_zfmisc_1(u1_struct_0(A_260))) | ~v2_tex_2(B_261, A_260) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_pre_topc(A_260) | ~v3_tdlat_3(A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260))), inference(cnfTransformation, [status(thm)], [f_220])).
% 13.16/5.56  tff(c_5095, plain, (![A_466, B_467]: (v1_tops_1('#skF_1'(A_466, B_467), A_466) | ~v3_tex_2('#skF_1'(A_466, B_467), A_466) | ~v2_tex_2(B_467, A_466) | ~m1_subset_1(B_467, k1_zfmisc_1(u1_struct_0(A_466))) | ~l1_pre_topc(A_466) | ~v3_tdlat_3(A_466) | ~v2_pre_topc(A_466) | v2_struct_0(A_466))), inference(resolution, [status(thm)], [c_1432, c_54])).
% 13.16/5.56  tff(c_5105, plain, (![A_200]: (v1_tops_1('#skF_1'('#skF_2', A_200), '#skF_2') | ~m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1039, c_5095])).
% 13.16/5.56  tff(c_5118, plain, (![A_200]: (v1_tops_1('#skF_1'('#skF_2', A_200), '#skF_2') | ~m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_5105])).
% 13.16/5.56  tff(c_5120, plain, (![A_468]: (v1_tops_1('#skF_1'('#skF_2', A_468), '#skF_2') | ~m1_subset_1(A_468, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tex_2(A_468, '#skF_2') | ~r1_tarski(A_468, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_5118])).
% 13.16/5.56  tff(c_5180, plain, (![A_200]: (v1_tops_1('#skF_1'('#skF_2', A_200), '#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_483, c_5120])).
% 13.16/5.56  tff(c_5686, plain, (![A_512, B_513]: (k2_pre_topc(A_512, '#skF_1'(A_512, B_513))=u1_struct_0(A_512) | ~v1_tops_1('#skF_1'(A_512, B_513), A_512) | ~v2_tex_2(B_513, A_512) | ~m1_subset_1(B_513, k1_zfmisc_1(u1_struct_0(A_512))) | ~l1_pre_topc(A_512) | ~v3_tdlat_3(A_512) | ~v2_pre_topc(A_512) | v2_struct_0(A_512))), inference(resolution, [status(thm)], [c_1432, c_48])).
% 13.16/5.56  tff(c_5692, plain, (![A_200]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_200))=u1_struct_0('#skF_2') | ~m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5180, c_5686])).
% 13.16/5.56  tff(c_5703, plain, (![A_200]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_200))=u1_struct_0('#skF_2') | ~m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_5692])).
% 13.16/5.56  tff(c_5705, plain, (![A_514]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_514))=u1_struct_0('#skF_2') | ~m1_subset_1(A_514, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tex_2(A_514, '#skF_2') | ~r1_tarski(A_514, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_5703])).
% 13.16/5.56  tff(c_5735, plain, (![A_203]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_203))=u1_struct_0('#skF_2') | ~v2_tex_2(A_203, '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_203, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_510, c_5705])).
% 13.16/5.56  tff(c_5779, plain, (![A_515]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_515))=u1_struct_0('#skF_2') | ~v2_tex_2(A_515, '#skF_2') | ~r1_tarski(A_515, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2723, c_5735])).
% 13.16/5.56  tff(c_5815, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', u1_struct_0('#skF_3')))=u1_struct_0('#skF_2') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_5779])).
% 13.16/5.56  tff(c_5842, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', u1_struct_0('#skF_3')))=u1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_5815])).
% 13.16/5.56  tff(c_5912, plain, (![A_518, B_519]: (k2_pre_topc(A_518, '#skF_1'(A_518, B_519))=k2_struct_0(A_518) | ~v1_tops_1('#skF_1'(A_518, B_519), A_518) | ~v2_tex_2(B_519, A_518) | ~m1_subset_1(B_519, k1_zfmisc_1(u1_struct_0(A_518))) | ~l1_pre_topc(A_518) | ~v3_tdlat_3(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518))), inference(resolution, [status(thm)], [c_1432, c_34])).
% 13.16/5.56  tff(c_5918, plain, (![A_200]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_200))=k2_struct_0('#skF_2') | ~m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5180, c_5912])).
% 13.16/5.56  tff(c_5929, plain, (![A_200]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_200))=k2_struct_0('#skF_2') | ~m1_subset_1(A_200, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2') | ~v2_tex_2(A_200, '#skF_2') | ~r1_tarski(A_200, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_5918])).
% 13.16/5.56  tff(c_5931, plain, (![A_520]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_520))=k2_struct_0('#skF_2') | ~m1_subset_1(A_520, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_tex_2(A_520, '#skF_2') | ~r1_tarski(A_520, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_94, c_5929])).
% 13.16/5.56  tff(c_5961, plain, (![A_203]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_203))=k2_struct_0('#skF_2') | ~v2_tex_2(A_203, '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_203, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_510, c_5931])).
% 13.16/5.56  tff(c_6005, plain, (![A_521]: (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', A_521))=k2_struct_0('#skF_2') | ~v2_tex_2(A_521, '#skF_2') | ~r1_tarski(A_521, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2723, c_5961])).
% 13.16/5.56  tff(c_6041, plain, (k2_pre_topc('#skF_2', '#skF_1'('#skF_2', u1_struct_0('#skF_3')))=k2_struct_0('#skF_2') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_6005])).
% 13.16/5.56  tff(c_6068, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_749, c_5842, c_6041])).
% 13.16/5.56  tff(c_68, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_185, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_170])).
% 13.16/5.56  tff(c_187, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_185])).
% 13.16/5.56  tff(c_6120, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6068, c_187])).
% 13.16/5.56  tff(c_6734, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6120, c_24])).
% 13.16/5.56  tff(c_6737, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_94, c_6734])).
% 13.16/5.56  tff(c_6740, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_6737])).
% 13.16/5.56  tff(c_6744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_6740])).
% 13.16/5.56  tff(c_6745, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_6')=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_185])).
% 13.16/5.56  tff(c_64, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_96, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k6_domain_1(u1_struct_0('#skF_2'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64])).
% 13.16/5.56  tff(c_6783, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k6_domain_1(u1_struct_0('#skF_3'), '#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6745, c_96])).
% 13.16/5.56  tff(c_22551, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))!=k2_pre_topc('#skF_2', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_22549, c_6783])).
% 13.16/5.56  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_78, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_76, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_72, plain, (v3_borsuk_1('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_22550, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_186])).
% 13.16/5.56  tff(c_28, plain, (![A_26, B_27]: (m1_subset_1(k6_domain_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.16/5.56  tff(c_22555, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22549, c_28])).
% 13.16/5.56  tff(c_22559, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_22555])).
% 13.16/5.56  tff(c_22560, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_22550, c_22559])).
% 13.16/5.56  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_297])).
% 13.16/5.56  tff(c_6746, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_185])).
% 13.16/5.56  tff(c_6762, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6745, c_28])).
% 13.16/5.56  tff(c_6766, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_6762])).
% 13.16/5.56  tff(c_6767, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_6746, c_6766])).
% 13.16/5.56  tff(c_24056, plain, (![A_1249, B_1250, C_1251, E_1252]: (k8_relset_1(u1_struct_0(A_1249), u1_struct_0(B_1250), C_1251, E_1252)=k2_pre_topc(A_1249, E_1252) | ~m1_subset_1(E_1252, k1_zfmisc_1(u1_struct_0(A_1249))) | ~m1_subset_1(E_1252, k1_zfmisc_1(u1_struct_0(B_1250))) | ~v3_borsuk_1(C_1251, A_1249, B_1250) | ~m1_subset_1(C_1251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1249), u1_struct_0(B_1250)))) | ~v5_pre_topc(C_1251, A_1249, B_1250) | ~v1_funct_2(C_1251, u1_struct_0(A_1249), u1_struct_0(B_1250)) | ~v1_funct_1(C_1251) | ~m1_pre_topc(B_1250, A_1249) | ~v4_tex_2(B_1250, A_1249) | v2_struct_0(B_1250) | ~l1_pre_topc(A_1249) | ~v3_tdlat_3(A_1249) | ~v2_pre_topc(A_1249) | v2_struct_0(A_1249))), inference(cnfTransformation, [status(thm)], [f_258])).
% 13.16/5.56  tff(c_24072, plain, (![B_1250, C_1251]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_1250), C_1251, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_1250))) | ~v3_borsuk_1(C_1251, '#skF_2', B_1250) | ~m1_subset_1(C_1251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_1250)))) | ~v5_pre_topc(C_1251, '#skF_2', B_1250) | ~v1_funct_2(C_1251, u1_struct_0('#skF_2'), u1_struct_0(B_1250)) | ~v1_funct_1(C_1251) | ~m1_pre_topc(B_1250, '#skF_2') | ~v4_tex_2(B_1250, '#skF_2') | v2_struct_0(B_1250) | ~l1_pre_topc('#skF_2') | ~v3_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6767, c_24056])).
% 13.16/5.56  tff(c_24094, plain, (![B_1250, C_1251]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_1250), C_1251, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_1250))) | ~v3_borsuk_1(C_1251, '#skF_2', B_1250) | ~m1_subset_1(C_1251, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_1250)))) | ~v5_pre_topc(C_1251, '#skF_2', B_1250) | ~v1_funct_2(C_1251, u1_struct_0('#skF_2'), u1_struct_0(B_1250)) | ~v1_funct_1(C_1251) | ~m1_pre_topc(B_1250, '#skF_2') | ~v4_tex_2(B_1250, '#skF_2') | v2_struct_0(B_1250) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_24072])).
% 13.16/5.56  tff(c_24204, plain, (![B_1265, C_1266]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0(B_1265), C_1266, k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(B_1265))) | ~v3_borsuk_1(C_1266, '#skF_2', B_1265) | ~m1_subset_1(C_1266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_1265)))) | ~v5_pre_topc(C_1266, '#skF_2', B_1265) | ~v1_funct_2(C_1266, u1_struct_0('#skF_2'), u1_struct_0(B_1265)) | ~v1_funct_1(C_1266) | ~m1_pre_topc(B_1265, '#skF_2') | ~v4_tex_2(B_1265, '#skF_2') | v2_struct_0(B_1265))), inference(negUnitSimplification, [status(thm)], [c_94, c_24094])).
% 13.16/5.56  tff(c_24215, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | ~m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_borsuk_1('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v4_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_24204])).
% 13.16/5.56  tff(c_24220, plain, (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', k1_tarski('#skF_6'))=k2_pre_topc('#skF_2', k1_tarski('#skF_6')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_72, c_22560, c_24215])).
% 13.16/5.56  tff(c_24222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_22551, c_24220])).
% 13.16/5.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.16/5.56  
% 13.16/5.56  Inference rules
% 13.16/5.56  ----------------------
% 13.16/5.56  #Ref     : 0
% 13.16/5.56  #Sup     : 4700
% 13.16/5.56  #Fact    : 0
% 13.16/5.56  #Define  : 0
% 13.16/5.56  #Split   : 61
% 13.16/5.56  #Chain   : 0
% 13.16/5.56  #Close   : 0
% 13.16/5.56  
% 13.16/5.56  Ordering : KBO
% 13.16/5.56  
% 13.16/5.56  Simplification rules
% 13.16/5.56  ----------------------
% 13.16/5.56  #Subsume      : 2100
% 13.16/5.56  #Demod        : 5191
% 13.16/5.56  #Tautology    : 802
% 13.16/5.56  #SimpNegUnit  : 795
% 13.16/5.56  #BackRed      : 181
% 13.16/5.56  
% 13.16/5.56  #Partial instantiations: 0
% 13.16/5.56  #Strategies tried      : 1
% 13.16/5.56  
% 13.16/5.56  Timing (in seconds)
% 13.16/5.56  ----------------------
% 13.16/5.57  Preprocessing        : 0.64
% 13.16/5.57  Parsing              : 0.33
% 13.16/5.57  CNF conversion       : 0.06
% 13.16/5.57  Main loop            : 4.04
% 13.16/5.57  Inferencing          : 1.14
% 13.16/5.57  Reduction            : 1.37
% 13.16/5.57  Demodulation         : 0.92
% 13.16/5.57  BG Simplification    : 0.12
% 13.16/5.57  Subsumption          : 1.17
% 13.16/5.57  Abstraction          : 0.16
% 13.16/5.57  MUC search           : 0.00
% 13.16/5.57  Cooper               : 0.00
% 13.16/5.57  Total                : 4.77
% 13.16/5.57  Index Insertion      : 0.00
% 13.16/5.57  Index Deletion       : 0.00
% 13.16/5.57  Index Matching       : 0.00
% 13.16/5.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
