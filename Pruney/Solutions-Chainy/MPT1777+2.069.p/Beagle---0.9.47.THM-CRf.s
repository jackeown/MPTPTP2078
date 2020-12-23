%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:42 EST 2020

% Result     : Theorem 8.47s
% Output     : CNFRefutation 8.63s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 790 expanded)
%              Number of leaves         :   44 ( 294 expanded)
%              Depth                    :   14
%              Number of atoms          :  315 (3717 expanded)
%              Number of equality atoms :   14 ( 398 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_272,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_154,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_223,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( ( v1_tsep_1(C,D)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,B,E,F)
                                  <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_161,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_46,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_80,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_68,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_118,plain,(
    ! [B_298,A_299] :
      ( l1_pre_topc(B_298)
      | ~ m1_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_118])).

tff(c_131,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_124])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_296] :
      ( u1_struct_0(A_296) = k2_struct_0(A_296)
      | ~ l1_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_139,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_95])).

tff(c_100,plain,(
    ! [A_297] :
      ( u1_struct_0(A_297) = k2_struct_0(A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_108,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_100])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_113,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_60])).

tff(c_145,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_113])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_135,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_58])).

tff(c_144,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_135])).

tff(c_127,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_118])).

tff(c_134,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_127])).

tff(c_36,plain,(
    ! [A_36] :
      ( m1_pre_topc(A_36,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_143,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_134,c_95])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_151,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_56])).

tff(c_373,plain,(
    ! [A_315,B_316] :
      ( m1_pre_topc(A_315,g1_pre_topc(u1_struct_0(B_316),u1_pre_topc(B_316)))
      | ~ m1_pre_topc(A_315,B_316)
      | ~ l1_pre_topc(B_316)
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_388,plain,(
    ! [A_315] :
      ( m1_pre_topc(A_315,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_315,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_315) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_373])).

tff(c_412,plain,(
    ! [A_317] :
      ( m1_pre_topc(A_317,'#skF_4')
      | ~ m1_pre_topc(A_317,'#skF_3')
      | ~ l1_pre_topc(A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_151,c_388])).

tff(c_419,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_412])).

tff(c_425,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_419])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_146,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_54])).

tff(c_50,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_83,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52])).

tff(c_152,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_83])).

tff(c_48,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_84,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_4686,plain,(
    ! [A_443,D_447,B_445,E_448,C_444,G_446] :
      ( r1_tmap_1(D_447,B_445,E_448,G_446)
      | ~ r1_tmap_1(C_444,B_445,k3_tmap_1(A_443,B_445,D_447,C_444,E_448),G_446)
      | ~ m1_subset_1(G_446,u1_struct_0(C_444))
      | ~ m1_subset_1(G_446,u1_struct_0(D_447))
      | ~ m1_pre_topc(C_444,D_447)
      | ~ v1_tsep_1(C_444,D_447)
      | ~ m1_subset_1(E_448,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_447),u1_struct_0(B_445))))
      | ~ v1_funct_2(E_448,u1_struct_0(D_447),u1_struct_0(B_445))
      | ~ v1_funct_1(E_448)
      | ~ m1_pre_topc(D_447,A_443)
      | v2_struct_0(D_447)
      | ~ m1_pre_topc(C_444,A_443)
      | v2_struct_0(C_444)
      | ~ l1_pre_topc(B_445)
      | ~ v2_pre_topc(B_445)
      | v2_struct_0(B_445)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_4688,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_4686])).

tff(c_4691,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_68,c_64,c_62,c_145,c_108,c_139,c_144,c_108,c_139,c_425,c_146,c_139,c_152,c_143,c_4688])).

tff(c_4692,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_70,c_66,c_46,c_4691])).

tff(c_179,plain,(
    ! [B_303,A_304] :
      ( r1_tarski(u1_struct_0(B_303),u1_struct_0(A_304))
      | ~ m1_pre_topc(B_303,A_304)
      | ~ l1_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_185,plain,(
    ! [B_303] :
      ( r1_tarski(u1_struct_0(B_303),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_303,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_179])).

tff(c_212,plain,(
    ! [B_305] :
      ( r1_tarski(u1_struct_0(B_305),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_305,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_185])).

tff(c_215,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_212])).

tff(c_303,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_306,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_306])).

tff(c_312,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_162,plain,(
    ! [B_301,A_302] :
      ( v2_pre_topc(B_301)
      | ~ m1_pre_topc(B_301,A_302)
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_171,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_162])).

tff(c_178,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_171])).

tff(c_14,plain,(
    ! [A_12] :
      ( v3_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(u1_struct_0(B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1347,plain,(
    ! [B_356,A_357] :
      ( v1_tsep_1(B_356,A_357)
      | ~ v3_pre_topc(u1_struct_0(B_356),A_357)
      | ~ m1_subset_1(u1_struct_0(B_356),k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ m1_pre_topc(B_356,A_357)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6306,plain,(
    ! [B_481,A_482] :
      ( v1_tsep_1(B_481,A_482)
      | ~ v3_pre_topc(u1_struct_0(B_481),A_482)
      | ~ v2_pre_topc(A_482)
      | ~ m1_pre_topc(B_481,A_482)
      | ~ l1_pre_topc(A_482) ) ),
    inference(resolution,[status(thm)],[c_32,c_1347])).

tff(c_7273,plain,(
    ! [A_499] :
      ( v1_tsep_1('#skF_3',A_499)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_499)
      | ~ v2_pre_topc(A_499)
      | ~ m1_pre_topc('#skF_3',A_499)
      | ~ l1_pre_topc(A_499) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_6306])).

tff(c_7277,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_7273])).

tff(c_7280,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_134,c_312,c_7277])).

tff(c_191,plain,(
    ! [B_303] :
      ( r1_tarski(u1_struct_0(B_303),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_303,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_179])).

tff(c_225,plain,(
    ! [B_306] :
      ( r1_tarski(u1_struct_0(B_306),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_306,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_191])).

tff(c_231,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_225])).

tff(c_603,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_606,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_603])).

tff(c_610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_606])).

tff(c_612,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_465,plain,(
    ! [A_319,B_320] :
      ( m1_pre_topc(A_319,B_320)
      | ~ m1_pre_topc(A_319,g1_pre_topc(u1_struct_0(B_320),u1_pre_topc(B_320)))
      | ~ l1_pre_topc(B_320)
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_475,plain,(
    ! [A_319] :
      ( m1_pre_topc(A_319,'#skF_3')
      | ~ m1_pre_topc(A_319,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_465])).

tff(c_494,plain,(
    ! [A_319] :
      ( m1_pre_topc(A_319,'#skF_3')
      | ~ m1_pre_topc(A_319,'#skF_4')
      | ~ l1_pre_topc(A_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_151,c_475])).

tff(c_218,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_212])).

tff(c_634,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_637,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_494,c_634])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_612,c_637])).

tff(c_643,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_38,plain,(
    ! [B_39,A_37] :
      ( r1_tarski(u1_struct_0(B_39),u1_struct_0(A_37))
      | ~ m1_pre_topc(B_39,A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1450,plain,(
    ! [B_358,C_359,A_360] :
      ( v1_tsep_1(B_358,C_359)
      | ~ r1_tarski(u1_struct_0(B_358),u1_struct_0(C_359))
      | ~ m1_pre_topc(C_359,A_360)
      | v2_struct_0(C_359)
      | ~ m1_pre_topc(B_358,A_360)
      | ~ v1_tsep_1(B_358,A_360)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | v2_struct_0(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_7928,plain,(
    ! [B_515,A_516,A_517] :
      ( v1_tsep_1(B_515,A_516)
      | ~ m1_pre_topc(A_516,A_517)
      | v2_struct_0(A_516)
      | ~ m1_pre_topc(B_515,A_517)
      | ~ v1_tsep_1(B_515,A_517)
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517)
      | ~ m1_pre_topc(B_515,A_516)
      | ~ l1_pre_topc(A_516) ) ),
    inference(resolution,[status(thm)],[c_38,c_1450])).

tff(c_7980,plain,(
    ! [B_515] :
      ( v1_tsep_1(B_515,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_515,'#skF_3')
      | ~ v1_tsep_1(B_515,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_515,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_643,c_7928])).

tff(c_8097,plain,(
    ! [B_515] :
      ( v1_tsep_1(B_515,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_515,'#skF_3')
      | ~ v1_tsep_1(B_515,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_515,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_178,c_134,c_7980])).

tff(c_8151,plain,(
    ! [B_520] :
      ( v1_tsep_1(B_520,'#skF_4')
      | ~ m1_pre_topc(B_520,'#skF_3')
      | ~ v1_tsep_1(B_520,'#skF_3')
      | ~ m1_pre_topc(B_520,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66,c_8097])).

tff(c_8157,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_7280,c_8151])).

tff(c_8161,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_312,c_8157])).

tff(c_8163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4692,c_8161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.47/2.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.47/2.88  
% 8.47/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.47/2.88  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.47/2.88  
% 8.47/2.88  %Foreground sorts:
% 8.47/2.88  
% 8.47/2.88  
% 8.47/2.88  %Background operators:
% 8.47/2.88  
% 8.47/2.88  
% 8.47/2.88  %Foreground operators:
% 8.47/2.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.47/2.88  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.47/2.88  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.47/2.88  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.47/2.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.47/2.88  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.47/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.47/2.88  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.47/2.88  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 8.47/2.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.47/2.88  tff('#skF_7', type, '#skF_7': $i).
% 8.47/2.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.47/2.88  tff('#skF_5', type, '#skF_5': $i).
% 8.47/2.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.47/2.88  tff('#skF_6', type, '#skF_6': $i).
% 8.47/2.88  tff('#skF_2', type, '#skF_2': $i).
% 8.47/2.88  tff('#skF_3', type, '#skF_3': $i).
% 8.47/2.88  tff('#skF_1', type, '#skF_1': $i).
% 8.47/2.88  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.47/2.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.47/2.88  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.47/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.47/2.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.47/2.88  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 8.47/2.88  tff('#skF_4', type, '#skF_4': $i).
% 8.47/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.47/2.88  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.47/2.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.47/2.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.47/2.88  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 8.47/2.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.47/2.88  
% 8.63/2.90  tff(f_272, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 8.63/2.90  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.63/2.90  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.63/2.90  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 8.63/2.90  tff(f_154, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.63/2.90  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 8.63/2.90  tff(f_223, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 8.63/2.90  tff(f_161, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 8.63/2.90  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.63/2.90  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 8.63/2.90  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 8.63/2.90  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 8.63/2.90  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 8.63/2.90  tff(c_82, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_46, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_80, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_68, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_118, plain, (![B_298, A_299]: (l1_pre_topc(B_298) | ~m1_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.63/2.90  tff(c_124, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_118])).
% 8.63/2.90  tff(c_131, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_124])).
% 8.63/2.90  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.63/2.90  tff(c_91, plain, (![A_296]: (u1_struct_0(A_296)=k2_struct_0(A_296) | ~l1_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.63/2.90  tff(c_95, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_91])).
% 8.63/2.90  tff(c_139, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_131, c_95])).
% 8.63/2.90  tff(c_100, plain, (![A_297]: (u1_struct_0(A_297)=k2_struct_0(A_297) | ~l1_pre_topc(A_297))), inference(resolution, [status(thm)], [c_6, c_91])).
% 8.63/2.90  tff(c_108, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_100])).
% 8.63/2.90  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_113, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_60])).
% 8.63/2.90  tff(c_145, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_113])).
% 8.63/2.90  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_135, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_58])).
% 8.63/2.90  tff(c_144, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_135])).
% 8.63/2.90  tff(c_127, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_118])).
% 8.63/2.90  tff(c_134, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_127])).
% 8.63/2.90  tff(c_36, plain, (![A_36]: (m1_pre_topc(A_36, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.63/2.90  tff(c_143, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_134, c_95])).
% 8.63/2.90  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_151, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_56])).
% 8.63/2.90  tff(c_373, plain, (![A_315, B_316]: (m1_pre_topc(A_315, g1_pre_topc(u1_struct_0(B_316), u1_pre_topc(B_316))) | ~m1_pre_topc(A_315, B_316) | ~l1_pre_topc(B_316) | ~l1_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.63/2.90  tff(c_388, plain, (![A_315]: (m1_pre_topc(A_315, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_315, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_315))), inference(superposition, [status(thm), theory('equality')], [c_143, c_373])).
% 8.63/2.90  tff(c_412, plain, (![A_317]: (m1_pre_topc(A_317, '#skF_4') | ~m1_pre_topc(A_317, '#skF_3') | ~l1_pre_topc(A_317))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_151, c_388])).
% 8.63/2.90  tff(c_419, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_412])).
% 8.63/2.90  tff(c_425, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_419])).
% 8.63/2.90  tff(c_54, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_146, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_54])).
% 8.63/2.90  tff(c_50, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_83, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52])).
% 8.63/2.90  tff(c_152, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_83])).
% 8.63/2.90  tff(c_48, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.63/2.90  tff(c_84, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 8.63/2.90  tff(c_4686, plain, (![A_443, D_447, B_445, E_448, C_444, G_446]: (r1_tmap_1(D_447, B_445, E_448, G_446) | ~r1_tmap_1(C_444, B_445, k3_tmap_1(A_443, B_445, D_447, C_444, E_448), G_446) | ~m1_subset_1(G_446, u1_struct_0(C_444)) | ~m1_subset_1(G_446, u1_struct_0(D_447)) | ~m1_pre_topc(C_444, D_447) | ~v1_tsep_1(C_444, D_447) | ~m1_subset_1(E_448, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_447), u1_struct_0(B_445)))) | ~v1_funct_2(E_448, u1_struct_0(D_447), u1_struct_0(B_445)) | ~v1_funct_1(E_448) | ~m1_pre_topc(D_447, A_443) | v2_struct_0(D_447) | ~m1_pre_topc(C_444, A_443) | v2_struct_0(C_444) | ~l1_pre_topc(B_445) | ~v2_pre_topc(B_445) | v2_struct_0(B_445) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(cnfTransformation, [status(thm)], [f_223])).
% 8.63/2.90  tff(c_4688, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_4686])).
% 8.63/2.90  tff(c_4691, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_68, c_64, c_62, c_145, c_108, c_139, c_144, c_108, c_139, c_425, c_146, c_139, c_152, c_143, c_4688])).
% 8.63/2.90  tff(c_4692, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_70, c_66, c_46, c_4691])).
% 8.63/2.90  tff(c_179, plain, (![B_303, A_304]: (r1_tarski(u1_struct_0(B_303), u1_struct_0(A_304)) | ~m1_pre_topc(B_303, A_304) | ~l1_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.63/2.90  tff(c_185, plain, (![B_303]: (r1_tarski(u1_struct_0(B_303), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_303, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_143, c_179])).
% 8.63/2.90  tff(c_212, plain, (![B_305]: (r1_tarski(u1_struct_0(B_305), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_305, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_185])).
% 8.63/2.90  tff(c_215, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_143, c_212])).
% 8.63/2.90  tff(c_303, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_215])).
% 8.63/2.90  tff(c_306, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_303])).
% 8.63/2.90  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_306])).
% 8.63/2.90  tff(c_312, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_215])).
% 8.63/2.90  tff(c_162, plain, (![B_301, A_302]: (v2_pre_topc(B_301) | ~m1_pre_topc(B_301, A_302) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.63/2.90  tff(c_171, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_162])).
% 8.63/2.90  tff(c_178, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_171])).
% 8.63/2.90  tff(c_14, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.63/2.90  tff(c_32, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.63/2.90  tff(c_1347, plain, (![B_356, A_357]: (v1_tsep_1(B_356, A_357) | ~v3_pre_topc(u1_struct_0(B_356), A_357) | ~m1_subset_1(u1_struct_0(B_356), k1_zfmisc_1(u1_struct_0(A_357))) | ~m1_pre_topc(B_356, A_357) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.63/2.90  tff(c_6306, plain, (![B_481, A_482]: (v1_tsep_1(B_481, A_482) | ~v3_pre_topc(u1_struct_0(B_481), A_482) | ~v2_pre_topc(A_482) | ~m1_pre_topc(B_481, A_482) | ~l1_pre_topc(A_482))), inference(resolution, [status(thm)], [c_32, c_1347])).
% 8.63/2.90  tff(c_7273, plain, (![A_499]: (v1_tsep_1('#skF_3', A_499) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_499) | ~v2_pre_topc(A_499) | ~m1_pre_topc('#skF_3', A_499) | ~l1_pre_topc(A_499))), inference(superposition, [status(thm), theory('equality')], [c_143, c_6306])).
% 8.63/2.90  tff(c_7277, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_7273])).
% 8.63/2.90  tff(c_7280, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_134, c_312, c_7277])).
% 8.63/2.90  tff(c_191, plain, (![B_303]: (r1_tarski(u1_struct_0(B_303), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_303, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_179])).
% 8.63/2.90  tff(c_225, plain, (![B_306]: (r1_tarski(u1_struct_0(B_306), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_306, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_191])).
% 8.63/2.90  tff(c_231, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_139, c_225])).
% 8.63/2.90  tff(c_603, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_231])).
% 8.63/2.90  tff(c_606, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_603])).
% 8.63/2.90  tff(c_610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_606])).
% 8.63/2.90  tff(c_612, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_231])).
% 8.63/2.90  tff(c_465, plain, (![A_319, B_320]: (m1_pre_topc(A_319, B_320) | ~m1_pre_topc(A_319, g1_pre_topc(u1_struct_0(B_320), u1_pre_topc(B_320))) | ~l1_pre_topc(B_320) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.63/2.90  tff(c_475, plain, (![A_319]: (m1_pre_topc(A_319, '#skF_3') | ~m1_pre_topc(A_319, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_319))), inference(superposition, [status(thm), theory('equality')], [c_143, c_465])).
% 8.63/2.90  tff(c_494, plain, (![A_319]: (m1_pre_topc(A_319, '#skF_3') | ~m1_pre_topc(A_319, '#skF_4') | ~l1_pre_topc(A_319))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_151, c_475])).
% 8.63/2.90  tff(c_218, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_139, c_212])).
% 8.63/2.90  tff(c_634, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_218])).
% 8.63/2.90  tff(c_637, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_494, c_634])).
% 8.63/2.90  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_612, c_637])).
% 8.63/2.90  tff(c_643, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_218])).
% 8.63/2.90  tff(c_38, plain, (![B_39, A_37]: (r1_tarski(u1_struct_0(B_39), u1_struct_0(A_37)) | ~m1_pre_topc(B_39, A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.63/2.90  tff(c_1450, plain, (![B_358, C_359, A_360]: (v1_tsep_1(B_358, C_359) | ~r1_tarski(u1_struct_0(B_358), u1_struct_0(C_359)) | ~m1_pre_topc(C_359, A_360) | v2_struct_0(C_359) | ~m1_pre_topc(B_358, A_360) | ~v1_tsep_1(B_358, A_360) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360) | v2_struct_0(A_360))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.63/2.90  tff(c_7928, plain, (![B_515, A_516, A_517]: (v1_tsep_1(B_515, A_516) | ~m1_pre_topc(A_516, A_517) | v2_struct_0(A_516) | ~m1_pre_topc(B_515, A_517) | ~v1_tsep_1(B_515, A_517) | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517) | ~m1_pre_topc(B_515, A_516) | ~l1_pre_topc(A_516))), inference(resolution, [status(thm)], [c_38, c_1450])).
% 8.63/2.90  tff(c_7980, plain, (![B_515]: (v1_tsep_1(B_515, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_515, '#skF_3') | ~v1_tsep_1(B_515, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_515, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_643, c_7928])).
% 8.63/2.90  tff(c_8097, plain, (![B_515]: (v1_tsep_1(B_515, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_515, '#skF_3') | ~v1_tsep_1(B_515, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_515, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_178, c_134, c_7980])).
% 8.63/2.90  tff(c_8151, plain, (![B_520]: (v1_tsep_1(B_520, '#skF_4') | ~m1_pre_topc(B_520, '#skF_3') | ~v1_tsep_1(B_520, '#skF_3') | ~m1_pre_topc(B_520, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_66, c_8097])).
% 8.63/2.90  tff(c_8157, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_7280, c_8151])).
% 8.63/2.90  tff(c_8161, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_312, c_8157])).
% 8.63/2.90  tff(c_8163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4692, c_8161])).
% 8.63/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.63/2.90  
% 8.63/2.90  Inference rules
% 8.63/2.90  ----------------------
% 8.63/2.90  #Ref     : 0
% 8.63/2.90  #Sup     : 1549
% 8.63/2.90  #Fact    : 0
% 8.63/2.90  #Define  : 0
% 8.63/2.90  #Split   : 30
% 8.63/2.90  #Chain   : 0
% 8.63/2.90  #Close   : 0
% 8.63/2.90  
% 8.63/2.90  Ordering : KBO
% 8.63/2.90  
% 8.63/2.90  Simplification rules
% 8.63/2.90  ----------------------
% 8.63/2.90  #Subsume      : 207
% 8.63/2.90  #Demod        : 2704
% 8.63/2.90  #Tautology    : 604
% 8.63/2.90  #SimpNegUnit  : 319
% 8.63/2.90  #BackRed      : 17
% 8.63/2.90  
% 8.63/2.90  #Partial instantiations: 0
% 8.63/2.90  #Strategies tried      : 1
% 8.63/2.90  
% 8.63/2.90  Timing (in seconds)
% 8.63/2.90  ----------------------
% 8.63/2.90  Preprocessing        : 0.40
% 8.63/2.90  Parsing              : 0.20
% 8.63/2.90  CNF conversion       : 0.05
% 8.63/2.90  Main loop            : 1.66
% 8.63/2.90  Inferencing          : 0.49
% 8.63/2.90  Reduction            : 0.68
% 8.63/2.90  Demodulation         : 0.51
% 8.63/2.90  BG Simplification    : 0.05
% 8.63/2.90  Subsumption          : 0.34
% 8.63/2.91  Abstraction          : 0.06
% 8.63/2.91  MUC search           : 0.00
% 8.63/2.91  Cooper               : 0.00
% 8.63/2.91  Total                : 2.10
% 8.63/2.91  Index Insertion      : 0.00
% 8.63/2.91  Index Deletion       : 0.00
% 8.63/2.91  Index Matching       : 0.00
% 8.63/2.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
