%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:39 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :  136 (1263 expanded)
%              Number of leaves         :   42 ( 454 expanded)
%              Depth                    :   19
%              Number of atoms          :  296 (5926 expanded)
%              Number of equality atoms :   19 ( 645 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_224,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_175,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_116,plain,(
    ! [B_292,A_293] :
      ( l1_pre_topc(B_292)
      | ~ m1_pre_topc(B_292,A_293)
      | ~ l1_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_132,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_125])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    ! [A_290] :
      ( u1_struct_0(A_290) = k2_struct_0(A_290)
      | ~ l1_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_140,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_93])).

tff(c_98,plain,(
    ! [A_291] :
      ( u1_struct_0(A_291) = k2_struct_0(A_291)
      | ~ l1_pre_topc(A_291) ) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_106,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_98])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_111,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_56])).

tff(c_149,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_111])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_147,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_54])).

tff(c_148,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_147])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_129,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_122])).

tff(c_30,plain,(
    ! [A_25] :
      ( m1_pre_topc(A_25,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_136,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_93])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_141,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_52])).

tff(c_409,plain,(
    ! [A_314,B_315] :
      ( m1_pre_topc(A_314,g1_pre_topc(u1_struct_0(B_315),u1_pre_topc(B_315)))
      | ~ m1_pre_topc(A_314,B_315)
      | ~ l1_pre_topc(B_315)
      | ~ l1_pre_topc(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_430,plain,(
    ! [A_314] :
      ( m1_pre_topc(A_314,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_314,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_314) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_409])).

tff(c_452,plain,(
    ! [A_316] :
      ( m1_pre_topc(A_316,'#skF_4')
      | ~ m1_pre_topc(A_316,'#skF_3')
      | ~ l1_pre_topc(A_316) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_141,c_430])).

tff(c_463,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_452])).

tff(c_470,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_463])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_150,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_50])).

tff(c_167,plain,(
    ! [B_297,A_298] :
      ( v2_pre_topc(B_297)
      | ~ m1_pre_topc(B_297,A_298)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_176,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_167])).

tff(c_183,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_176])).

tff(c_184,plain,(
    ! [B_299,A_300] :
      ( m1_subset_1(u1_struct_0(B_299),k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_190,plain,(
    ! [B_299] :
      ( m1_subset_1(u1_struct_0(B_299),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_299,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_184])).

tff(c_217,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_301,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_190])).

tff(c_220,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_217])).

tff(c_594,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_597,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_594])).

tff(c_601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_597])).

tff(c_603,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_625,plain,(
    ! [B_320,C_321,A_322] :
      ( r1_tarski(u1_struct_0(B_320),u1_struct_0(C_321))
      | ~ m1_pre_topc(B_320,C_321)
      | ~ m1_pre_topc(C_321,A_322)
      | ~ m1_pre_topc(B_320,A_322)
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_627,plain,(
    ! [B_320] :
      ( r1_tarski(u1_struct_0(B_320),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_320,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_603,c_625])).

tff(c_676,plain,(
    ! [B_323] :
      ( r1_tarski(u1_struct_0(B_323),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_323,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_132,c_140,c_627])).

tff(c_684,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_676])).

tff(c_695,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_684])).

tff(c_302,plain,(
    ! [A_309,B_310] :
      ( m1_pre_topc(A_309,B_310)
      | ~ m1_pre_topc(A_309,g1_pre_topc(u1_struct_0(B_310),u1_pre_topc(B_310)))
      | ~ l1_pre_topc(B_310)
      | ~ l1_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_308,plain,(
    ! [A_309] :
      ( m1_pre_topc(A_309,'#skF_3')
      | ~ m1_pre_topc(A_309,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_309) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_302])).

tff(c_322,plain,(
    ! [A_309] :
      ( m1_pre_topc(A_309,'#skF_3')
      | ~ m1_pre_topc(A_309,'#skF_4')
      | ~ l1_pre_topc(A_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_141,c_308])).

tff(c_173,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_167])).

tff(c_180,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_173])).

tff(c_196,plain,(
    ! [B_299] :
      ( m1_subset_1(u1_struct_0(B_299),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_299,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_184])).

tff(c_257,plain,(
    ! [B_306] :
      ( m1_subset_1(u1_struct_0(B_306),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_306,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_196])).

tff(c_263,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_257])).

tff(c_524,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_530,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_322,c_524])).

tff(c_540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_470,c_530])).

tff(c_542,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_629,plain,(
    ! [B_320] :
      ( r1_tarski(u1_struct_0(B_320),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_320,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_542,c_625])).

tff(c_746,plain,(
    ! [B_326] :
      ( r1_tarski(u1_struct_0(B_326),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_326,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_129,c_136,c_629])).

tff(c_751,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_746])).

tff(c_806,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_751])).

tff(c_810,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_322,c_806])).

tff(c_814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_603,c_810])).

tff(c_815,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_751])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_844,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_815,c_2])).

tff(c_847,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_844])).

tff(c_858,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_136])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_1071,plain,(
    ! [B_345,A_343,D_347,E_344,C_348,G_346] :
      ( r1_tmap_1(D_347,B_345,E_344,G_346)
      | ~ r1_tmap_1(C_348,B_345,k3_tmap_1(A_343,B_345,D_347,C_348,E_344),G_346)
      | ~ m1_subset_1(G_346,u1_struct_0(C_348))
      | ~ m1_subset_1(G_346,u1_struct_0(D_347))
      | ~ m1_pre_topc(C_348,D_347)
      | ~ v1_tsep_1(C_348,D_347)
      | ~ m1_subset_1(E_344,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_347),u1_struct_0(B_345))))
      | ~ v1_funct_2(E_344,u1_struct_0(D_347),u1_struct_0(B_345))
      | ~ v1_funct_1(E_344)
      | ~ m1_pre_topc(D_347,A_343)
      | v2_struct_0(D_347)
      | ~ m1_pre_topc(C_348,A_343)
      | v2_struct_0(C_348)
      | ~ l1_pre_topc(B_345)
      | ~ v2_pre_topc(B_345)
      | v2_struct_0(B_345)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1073,plain,
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
    inference(resolution,[status(thm)],[c_80,c_1071])).

tff(c_1076,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_149,c_106,c_140,c_148,c_106,c_140,c_470,c_150,c_140,c_150,c_858,c_1073])).

tff(c_1077,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_42,c_1076])).

tff(c_20,plain,(
    ! [A_14] :
      ( v3_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_764,plain,(
    ! [B_327,A_328] :
      ( v1_tsep_1(B_327,A_328)
      | ~ v3_pre_topc(u1_struct_0(B_327),A_328)
      | ~ m1_subset_1(u1_struct_0(B_327),k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ m1_pre_topc(B_327,A_328)
      | ~ l1_pre_topc(A_328)
      | ~ v2_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1603,plain,(
    ! [B_382,A_383] :
      ( v1_tsep_1(B_382,A_383)
      | ~ v3_pre_topc(u1_struct_0(B_382),A_383)
      | ~ v2_pre_topc(A_383)
      | ~ m1_pre_topc(B_382,A_383)
      | ~ l1_pre_topc(A_383) ) ),
    inference(resolution,[status(thm)],[c_28,c_764])).

tff(c_2219,plain,(
    ! [A_427] :
      ( v1_tsep_1('#skF_3',A_427)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_427)
      | ~ v2_pre_topc(A_427)
      | ~ m1_pre_topc('#skF_3',A_427)
      | ~ l1_pre_topc(A_427) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_1603])).

tff(c_2229,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_2219])).

tff(c_2236,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_132,c_470,c_2229])).

tff(c_2238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1077,c_2236])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:18:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.83  
% 4.80/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.83  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.80/1.83  
% 4.80/1.83  %Foreground sorts:
% 4.80/1.83  
% 4.80/1.83  
% 4.80/1.83  %Background operators:
% 4.80/1.83  
% 4.80/1.83  
% 4.80/1.83  %Foreground operators:
% 4.80/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.80/1.83  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.80/1.83  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.80/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.80/1.83  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.80/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.83  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.80/1.83  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.80/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.80/1.83  tff('#skF_7', type, '#skF_7': $i).
% 4.80/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.80/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.80/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.80/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.80/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.80/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.80/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.80/1.83  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.80/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.80/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.83  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.80/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.80/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.80/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.80/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.80/1.83  
% 4.98/1.86  tff(f_224, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.98/1.86  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.98/1.86  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.98/1.86  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.98/1.86  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.98/1.86  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.98/1.86  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.98/1.86  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.98/1.86  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.98/1.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.98/1.86  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.98/1.86  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.98/1.86  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.98/1.86  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_116, plain, (![B_292, A_293]: (l1_pre_topc(B_292) | ~m1_pre_topc(B_292, A_293) | ~l1_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.98/1.86  tff(c_125, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_116])).
% 4.98/1.86  tff(c_132, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_125])).
% 4.98/1.86  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.98/1.86  tff(c_89, plain, (![A_290]: (u1_struct_0(A_290)=k2_struct_0(A_290) | ~l1_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.98/1.86  tff(c_93, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_12, c_89])).
% 4.98/1.86  tff(c_140, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_132, c_93])).
% 4.98/1.86  tff(c_98, plain, (![A_291]: (u1_struct_0(A_291)=k2_struct_0(A_291) | ~l1_pre_topc(A_291))), inference(resolution, [status(thm)], [c_12, c_89])).
% 4.98/1.86  tff(c_106, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_98])).
% 4.98/1.86  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_111, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_56])).
% 4.98/1.86  tff(c_149, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_111])).
% 4.98/1.86  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_147, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_54])).
% 4.98/1.86  tff(c_148, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_147])).
% 4.98/1.86  tff(c_122, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_116])).
% 4.98/1.86  tff(c_129, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_122])).
% 4.98/1.86  tff(c_30, plain, (![A_25]: (m1_pre_topc(A_25, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.98/1.86  tff(c_136, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_129, c_93])).
% 4.98/1.86  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_141, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_52])).
% 4.98/1.86  tff(c_409, plain, (![A_314, B_315]: (m1_pre_topc(A_314, g1_pre_topc(u1_struct_0(B_315), u1_pre_topc(B_315))) | ~m1_pre_topc(A_314, B_315) | ~l1_pre_topc(B_315) | ~l1_pre_topc(A_314))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.98/1.86  tff(c_430, plain, (![A_314]: (m1_pre_topc(A_314, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_314, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_314))), inference(superposition, [status(thm), theory('equality')], [c_136, c_409])).
% 4.98/1.86  tff(c_452, plain, (![A_316]: (m1_pre_topc(A_316, '#skF_4') | ~m1_pre_topc(A_316, '#skF_3') | ~l1_pre_topc(A_316))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_141, c_430])).
% 4.98/1.86  tff(c_463, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_452])).
% 4.98/1.86  tff(c_470, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_463])).
% 4.98/1.86  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_150, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_50])).
% 4.98/1.86  tff(c_167, plain, (![B_297, A_298]: (v2_pre_topc(B_297) | ~m1_pre_topc(B_297, A_298) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.98/1.86  tff(c_176, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_167])).
% 4.98/1.86  tff(c_183, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_176])).
% 4.98/1.86  tff(c_184, plain, (![B_299, A_300]: (m1_subset_1(u1_struct_0(B_299), k1_zfmisc_1(u1_struct_0(A_300))) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.98/1.86  tff(c_190, plain, (![B_299]: (m1_subset_1(u1_struct_0(B_299), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_299, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_184])).
% 4.98/1.86  tff(c_217, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_301, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_190])).
% 4.98/1.86  tff(c_220, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_140, c_217])).
% 4.98/1.86  tff(c_594, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_220])).
% 4.98/1.86  tff(c_597, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_594])).
% 4.98/1.86  tff(c_601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_597])).
% 4.98/1.86  tff(c_603, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_220])).
% 4.98/1.86  tff(c_625, plain, (![B_320, C_321, A_322]: (r1_tarski(u1_struct_0(B_320), u1_struct_0(C_321)) | ~m1_pre_topc(B_320, C_321) | ~m1_pre_topc(C_321, A_322) | ~m1_pre_topc(B_320, A_322) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.98/1.86  tff(c_627, plain, (![B_320]: (r1_tarski(u1_struct_0(B_320), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_320, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_603, c_625])).
% 4.98/1.86  tff(c_676, plain, (![B_323]: (r1_tarski(u1_struct_0(B_323), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_323, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_132, c_140, c_627])).
% 4.98/1.86  tff(c_684, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_136, c_676])).
% 4.98/1.86  tff(c_695, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_684])).
% 4.98/1.86  tff(c_302, plain, (![A_309, B_310]: (m1_pre_topc(A_309, B_310) | ~m1_pre_topc(A_309, g1_pre_topc(u1_struct_0(B_310), u1_pre_topc(B_310))) | ~l1_pre_topc(B_310) | ~l1_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.98/1.86  tff(c_308, plain, (![A_309]: (m1_pre_topc(A_309, '#skF_3') | ~m1_pre_topc(A_309, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_309))), inference(superposition, [status(thm), theory('equality')], [c_136, c_302])).
% 4.98/1.86  tff(c_322, plain, (![A_309]: (m1_pre_topc(A_309, '#skF_3') | ~m1_pre_topc(A_309, '#skF_4') | ~l1_pre_topc(A_309))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_141, c_308])).
% 4.98/1.86  tff(c_173, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_167])).
% 4.98/1.86  tff(c_180, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_173])).
% 4.98/1.86  tff(c_196, plain, (![B_299]: (m1_subset_1(u1_struct_0(B_299), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_299, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_184])).
% 4.98/1.86  tff(c_257, plain, (![B_306]: (m1_subset_1(u1_struct_0(B_306), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_306, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_196])).
% 4.98/1.86  tff(c_263, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_136, c_257])).
% 4.98/1.86  tff(c_524, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_263])).
% 4.98/1.86  tff(c_530, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_322, c_524])).
% 4.98/1.86  tff(c_540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_470, c_530])).
% 4.98/1.86  tff(c_542, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_263])).
% 4.98/1.86  tff(c_629, plain, (![B_320]: (r1_tarski(u1_struct_0(B_320), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_320, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_542, c_625])).
% 4.98/1.86  tff(c_746, plain, (![B_326]: (r1_tarski(u1_struct_0(B_326), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_326, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_129, c_136, c_629])).
% 4.98/1.86  tff(c_751, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_746])).
% 4.98/1.86  tff(c_806, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_751])).
% 4.98/1.86  tff(c_810, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_322, c_806])).
% 4.98/1.86  tff(c_814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_603, c_810])).
% 4.98/1.86  tff(c_815, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_751])).
% 4.98/1.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.98/1.86  tff(c_844, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_815, c_2])).
% 4.98/1.86  tff(c_847, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_844])).
% 4.98/1.86  tff(c_858, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_136])).
% 4.98/1.86  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.98/1.86  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 4.98/1.86  tff(c_1071, plain, (![B_345, A_343, D_347, E_344, C_348, G_346]: (r1_tmap_1(D_347, B_345, E_344, G_346) | ~r1_tmap_1(C_348, B_345, k3_tmap_1(A_343, B_345, D_347, C_348, E_344), G_346) | ~m1_subset_1(G_346, u1_struct_0(C_348)) | ~m1_subset_1(G_346, u1_struct_0(D_347)) | ~m1_pre_topc(C_348, D_347) | ~v1_tsep_1(C_348, D_347) | ~m1_subset_1(E_344, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_347), u1_struct_0(B_345)))) | ~v1_funct_2(E_344, u1_struct_0(D_347), u1_struct_0(B_345)) | ~v1_funct_1(E_344) | ~m1_pre_topc(D_347, A_343) | v2_struct_0(D_347) | ~m1_pre_topc(C_348, A_343) | v2_struct_0(C_348) | ~l1_pre_topc(B_345) | ~v2_pre_topc(B_345) | v2_struct_0(B_345) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.98/1.86  tff(c_1073, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_1071])).
% 4.98/1.86  tff(c_1076, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_149, c_106, c_140, c_148, c_106, c_140, c_470, c_150, c_140, c_150, c_858, c_1073])).
% 4.98/1.86  tff(c_1077, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_42, c_1076])).
% 4.98/1.86  tff(c_20, plain, (![A_14]: (v3_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.98/1.86  tff(c_28, plain, (![B_24, A_22]: (m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.98/1.86  tff(c_764, plain, (![B_327, A_328]: (v1_tsep_1(B_327, A_328) | ~v3_pre_topc(u1_struct_0(B_327), A_328) | ~m1_subset_1(u1_struct_0(B_327), k1_zfmisc_1(u1_struct_0(A_328))) | ~m1_pre_topc(B_327, A_328) | ~l1_pre_topc(A_328) | ~v2_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.98/1.86  tff(c_1603, plain, (![B_382, A_383]: (v1_tsep_1(B_382, A_383) | ~v3_pre_topc(u1_struct_0(B_382), A_383) | ~v2_pre_topc(A_383) | ~m1_pre_topc(B_382, A_383) | ~l1_pre_topc(A_383))), inference(resolution, [status(thm)], [c_28, c_764])).
% 4.98/1.86  tff(c_2219, plain, (![A_427]: (v1_tsep_1('#skF_3', A_427) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_427) | ~v2_pre_topc(A_427) | ~m1_pre_topc('#skF_3', A_427) | ~l1_pre_topc(A_427))), inference(superposition, [status(thm), theory('equality')], [c_858, c_1603])).
% 4.98/1.86  tff(c_2229, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_2219])).
% 4.98/1.86  tff(c_2236, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_132, c_470, c_2229])).
% 4.98/1.86  tff(c_2238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1077, c_2236])).
% 4.98/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.98/1.86  
% 4.98/1.86  Inference rules
% 4.98/1.86  ----------------------
% 4.98/1.86  #Ref     : 0
% 4.98/1.86  #Sup     : 446
% 4.98/1.86  #Fact    : 0
% 4.98/1.86  #Define  : 0
% 4.98/1.86  #Split   : 18
% 4.98/1.86  #Chain   : 0
% 4.98/1.86  #Close   : 0
% 4.98/1.86  
% 4.98/1.86  Ordering : KBO
% 4.98/1.86  
% 4.98/1.86  Simplification rules
% 4.98/1.86  ----------------------
% 4.98/1.86  #Subsume      : 106
% 4.98/1.86  #Demod        : 705
% 4.98/1.86  #Tautology    : 154
% 4.98/1.86  #SimpNegUnit  : 22
% 4.98/1.86  #BackRed      : 17
% 4.98/1.86  
% 4.98/1.86  #Partial instantiations: 0
% 4.98/1.86  #Strategies tried      : 1
% 4.98/1.86  
% 4.98/1.86  Timing (in seconds)
% 4.98/1.86  ----------------------
% 4.98/1.86  Preprocessing        : 0.39
% 4.98/1.86  Parsing              : 0.19
% 4.98/1.86  CNF conversion       : 0.05
% 4.98/1.86  Main loop            : 0.71
% 4.98/1.86  Inferencing          : 0.24
% 4.98/1.86  Reduction            : 0.25
% 4.98/1.86  Demodulation         : 0.18
% 4.98/1.86  BG Simplification    : 0.03
% 4.98/1.86  Subsumption          : 0.14
% 4.98/1.86  Abstraction          : 0.03
% 4.98/1.86  MUC search           : 0.00
% 4.98/1.86  Cooper               : 0.00
% 4.98/1.86  Total                : 1.14
% 4.98/1.86  Index Insertion      : 0.00
% 4.98/1.86  Index Deletion       : 0.00
% 4.98/1.86  Index Matching       : 0.00
% 4.98/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
