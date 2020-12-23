%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:38 EST 2020

% Result     : Theorem 12.07s
% Output     : CNFRefutation 12.17s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 920 expanded)
%              Number of leaves         :   46 ( 336 expanded)
%              Depth                    :   15
%              Number of atoms          :  308 (4208 expanded)
%              Number of equality atoms :   24 ( 472 expanded)
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

tff(f_267,negated_conjecture,(
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

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_135,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_116,axiom,(
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
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_218,axiom,(
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

tff(f_61,axiom,(
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

tff(c_84,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_82,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_122,plain,(
    ! [B_305,A_306] :
      ( l1_pre_topc(B_305)
      | ~ m1_pre_topc(B_305,A_306)
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_128,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_122])).

tff(c_135,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_128])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_99,plain,(
    ! [A_303] :
      ( u1_struct_0(A_303) = k2_struct_0(A_303)
      | ~ l1_struct_0(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_103,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_142,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_103])).

tff(c_104,plain,(
    ! [A_304] :
      ( u1_struct_0(A_304) = k2_struct_0(A_304)
      | ~ l1_pre_topc(A_304) ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_112,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_104])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_117,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_62])).

tff(c_147,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_117])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_153,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_112,c_60])).

tff(c_131,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_122])).

tff(c_138,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_131])).

tff(c_146,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_103])).

tff(c_189,plain,(
    ! [B_312,A_313] :
      ( r1_tarski(u1_struct_0(B_312),u1_struct_0(A_313))
      | ~ m1_pre_topc(B_312,A_313)
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_203,plain,(
    ! [B_312] :
      ( r1_tarski(u1_struct_0(B_312),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_312,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_189])).

tff(c_242,plain,(
    ! [B_315] :
      ( r1_tarski(u1_struct_0(B_315),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_315,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_203])).

tff(c_247,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_242])).

tff(c_437,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_172,plain,(
    ! [B_310,A_311] :
      ( v2_pre_topc(B_310)
      | ~ m1_pre_topc(B_310,A_311)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_181,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_172])).

tff(c_188,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_181])).

tff(c_34,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_336,plain,(
    ! [B_321,A_322] :
      ( m1_subset_1(u1_struct_0(B_321),k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ m1_pre_topc(B_321,A_322)
      | ~ l1_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_342,plain,(
    ! [B_321] :
      ( m1_subset_1(u1_struct_0(B_321),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_321,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_336])).

tff(c_514,plain,(
    ! [B_333] :
      ( m1_subset_1(u1_struct_0(B_333),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_333,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_342])).

tff(c_517,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_514])).

tff(c_758,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_517])).

tff(c_764,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_758])).

tff(c_771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_764])).

tff(c_773,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_517])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_154,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_58])).

tff(c_1204,plain,(
    ! [A_361,B_362] :
      ( k1_tsep_1(A_361,B_362,B_362) = g1_pre_topc(u1_struct_0(B_362),u1_pre_topc(B_362))
      | ~ m1_pre_topc(B_362,A_361)
      | v2_struct_0(B_362)
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361)
      | v2_struct_0(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1206,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_3','#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_773,c_1204])).

tff(c_1227,plain,
    ( k1_tsep_1('#skF_3','#skF_3','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_138,c_154,c_146,c_1206])).

tff(c_1228,plain,(
    k1_tsep_1('#skF_3','#skF_3','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1227])).

tff(c_1291,plain,(
    ! [B_363,A_364,C_365] :
      ( m1_pre_topc(B_363,k1_tsep_1(A_364,B_363,C_365))
      | ~ m1_pre_topc(C_365,A_364)
      | v2_struct_0(C_365)
      | ~ m1_pre_topc(B_363,A_364)
      | v2_struct_0(B_363)
      | ~ l1_pre_topc(A_364)
      | ~ v2_pre_topc(A_364)
      | v2_struct_0(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1320,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_1291])).

tff(c_1339,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_138,c_773,c_773,c_1320])).

tff(c_1341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_437,c_1339])).

tff(c_1343,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_148,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_56])).

tff(c_197,plain,(
    ! [B_312] :
      ( r1_tarski(u1_struct_0(B_312),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_312,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_189])).

tff(c_225,plain,(
    ! [B_314] :
      ( r1_tarski(u1_struct_0(B_314),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_314,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_197])).

tff(c_233,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_225])).

tff(c_374,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_376,plain,(
    ! [B_323,A_324] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_323),u1_pre_topc(B_323)),A_324)
      | ~ m1_pre_topc(B_323,A_324)
      | ~ l1_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_387,plain,(
    ! [A_324] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_324)
      | ~ m1_pre_topc('#skF_3',A_324)
      | ~ l1_pre_topc(A_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_376])).

tff(c_401,plain,(
    ! [A_325] :
      ( m1_pre_topc('#skF_4',A_325)
      | ~ m1_pre_topc('#skF_3',A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_387])).

tff(c_405,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_401])).

tff(c_411,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_405])).

tff(c_413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_411])).

tff(c_414,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_1342,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1362,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1342,c_2])).

tff(c_1365,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_1362])).

tff(c_1372,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1365,c_146])).

tff(c_52,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_50,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_86,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50])).

tff(c_3207,plain,(
    ! [C_431,G_432,A_429,D_433,E_434,B_430] :
      ( r1_tmap_1(D_433,B_430,E_434,G_432)
      | ~ r1_tmap_1(C_431,B_430,k3_tmap_1(A_429,B_430,D_433,C_431,E_434),G_432)
      | ~ m1_subset_1(G_432,u1_struct_0(C_431))
      | ~ m1_subset_1(G_432,u1_struct_0(D_433))
      | ~ m1_pre_topc(C_431,D_433)
      | ~ v1_tsep_1(C_431,D_433)
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_433),u1_struct_0(B_430))))
      | ~ v1_funct_2(E_434,u1_struct_0(D_433),u1_struct_0(B_430))
      | ~ v1_funct_1(E_434)
      | ~ m1_pre_topc(D_433,A_429)
      | v2_struct_0(D_433)
      | ~ m1_pre_topc(C_431,A_429)
      | v2_struct_0(C_431)
      | ~ l1_pre_topc(B_430)
      | ~ v2_pre_topc(B_430)
      | v2_struct_0(B_430)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_3209,plain,
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
    inference(resolution,[status(thm)],[c_86,c_3207])).

tff(c_3212,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_70,c_66,c_64,c_147,c_112,c_142,c_153,c_112,c_142,c_1343,c_148,c_142,c_148,c_1372,c_3209])).

tff(c_3213,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_72,c_68,c_48,c_3212])).

tff(c_178,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_172])).

tff(c_185,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_178])).

tff(c_16,plain,(
    ! [A_11] :
      ( v3_pre_topc(k2_struct_0(A_11),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1973,plain,(
    ! [B_390,A_391] :
      ( v1_tsep_1(B_390,A_391)
      | ~ v3_pre_topc(u1_struct_0(B_390),A_391)
      | ~ m1_subset_1(u1_struct_0(B_390),k1_zfmisc_1(u1_struct_0(A_391)))
      | ~ m1_pre_topc(B_390,A_391)
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4050,plain,(
    ! [B_455,A_456] :
      ( v1_tsep_1(B_455,A_456)
      | ~ v3_pre_topc(u1_struct_0(B_455),A_456)
      | ~ v2_pre_topc(A_456)
      | ~ m1_pre_topc(B_455,A_456)
      | ~ l1_pre_topc(A_456) ) ),
    inference(resolution,[status(thm)],[c_28,c_1973])).

tff(c_18523,plain,(
    ! [A_604] :
      ( v1_tsep_1('#skF_3',A_604)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_604)
      | ~ v2_pre_topc(A_604)
      | ~ m1_pre_topc('#skF_3',A_604)
      | ~ l1_pre_topc(A_604) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1372,c_4050])).

tff(c_18539,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_18523])).

tff(c_18550,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_135,c_1343,c_18539])).

tff(c_18552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3213,c_18550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.07/4.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.17/4.74  
% 12.17/4.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.17/4.74  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.17/4.74  
% 12.17/4.74  %Foreground sorts:
% 12.17/4.74  
% 12.17/4.74  
% 12.17/4.74  %Background operators:
% 12.17/4.74  
% 12.17/4.74  
% 12.17/4.74  %Foreground operators:
% 12.17/4.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.17/4.74  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 12.17/4.74  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 12.17/4.74  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 12.17/4.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.17/4.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.17/4.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.17/4.74  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 12.17/4.74  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 12.17/4.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.17/4.74  tff('#skF_7', type, '#skF_7': $i).
% 12.17/4.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.17/4.74  tff('#skF_5', type, '#skF_5': $i).
% 12.17/4.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.17/4.74  tff('#skF_6', type, '#skF_6': $i).
% 12.17/4.74  tff('#skF_2', type, '#skF_2': $i).
% 12.17/4.74  tff('#skF_3', type, '#skF_3': $i).
% 12.17/4.74  tff('#skF_1', type, '#skF_1': $i).
% 12.17/4.74  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 12.17/4.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.17/4.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.17/4.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.17/4.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.17/4.74  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 12.17/4.74  tff('#skF_4', type, '#skF_4': $i).
% 12.17/4.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.17/4.74  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.17/4.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.17/4.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.17/4.74  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.17/4.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.17/4.74  
% 12.17/4.76  tff(f_267, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 12.17/4.76  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.17/4.76  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.17/4.76  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 12.17/4.76  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 12.17/4.76  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 12.17/4.76  tff(f_135, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 12.17/4.76  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 12.17/4.76  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 12.17/4.76  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 12.17/4.76  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 12.17/4.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.17/4.76  tff(f_218, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 12.17/4.76  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 12.17/4.76  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 12.17/4.76  tff(c_84, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_48, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_82, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_122, plain, (![B_305, A_306]: (l1_pre_topc(B_305) | ~m1_pre_topc(B_305, A_306) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.17/4.76  tff(c_128, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_122])).
% 12.17/4.76  tff(c_135, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_128])).
% 12.17/4.76  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.17/4.76  tff(c_99, plain, (![A_303]: (u1_struct_0(A_303)=k2_struct_0(A_303) | ~l1_struct_0(A_303))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.17/4.76  tff(c_103, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_12, c_99])).
% 12.17/4.76  tff(c_142, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_135, c_103])).
% 12.17/4.76  tff(c_104, plain, (![A_304]: (u1_struct_0(A_304)=k2_struct_0(A_304) | ~l1_pre_topc(A_304))), inference(resolution, [status(thm)], [c_12, c_99])).
% 12.17/4.76  tff(c_112, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_104])).
% 12.17/4.76  tff(c_62, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_117, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_62])).
% 12.17/4.76  tff(c_147, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_117])).
% 12.17/4.76  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_153, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_112, c_60])).
% 12.17/4.76  tff(c_131, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_122])).
% 12.17/4.76  tff(c_138, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_131])).
% 12.17/4.76  tff(c_146, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_138, c_103])).
% 12.17/4.76  tff(c_189, plain, (![B_312, A_313]: (r1_tarski(u1_struct_0(B_312), u1_struct_0(A_313)) | ~m1_pre_topc(B_312, A_313) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.17/4.76  tff(c_203, plain, (![B_312]: (r1_tarski(u1_struct_0(B_312), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_312, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_189])).
% 12.17/4.76  tff(c_242, plain, (![B_315]: (r1_tarski(u1_struct_0(B_315), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_315, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_203])).
% 12.17/4.76  tff(c_247, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_146, c_242])).
% 12.17/4.76  tff(c_437, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_247])).
% 12.17/4.76  tff(c_172, plain, (![B_310, A_311]: (v2_pre_topc(B_310) | ~m1_pre_topc(B_310, A_311) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.17/4.76  tff(c_181, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_172])).
% 12.17/4.76  tff(c_188, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_181])).
% 12.17/4.76  tff(c_34, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_135])).
% 12.17/4.76  tff(c_336, plain, (![B_321, A_322]: (m1_subset_1(u1_struct_0(B_321), k1_zfmisc_1(u1_struct_0(A_322))) | ~m1_pre_topc(B_321, A_322) | ~l1_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.17/4.76  tff(c_342, plain, (![B_321]: (m1_subset_1(u1_struct_0(B_321), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_321, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_336])).
% 12.17/4.76  tff(c_514, plain, (![B_333]: (m1_subset_1(u1_struct_0(B_333), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_333, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_342])).
% 12.17/4.76  tff(c_517, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_146, c_514])).
% 12.17/4.76  tff(c_758, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_517])).
% 12.17/4.76  tff(c_764, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_758])).
% 12.17/4.76  tff(c_771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_764])).
% 12.17/4.76  tff(c_773, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_517])).
% 12.17/4.76  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_154, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_58])).
% 12.17/4.76  tff(c_1204, plain, (![A_361, B_362]: (k1_tsep_1(A_361, B_362, B_362)=g1_pre_topc(u1_struct_0(B_362), u1_pre_topc(B_362)) | ~m1_pre_topc(B_362, A_361) | v2_struct_0(B_362) | ~l1_pre_topc(A_361) | ~v2_pre_topc(A_361) | v2_struct_0(A_361))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.17/4.76  tff(c_1206, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_3', '#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_773, c_1204])).
% 12.17/4.76  tff(c_1227, plain, (k1_tsep_1('#skF_3', '#skF_3', '#skF_3')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_138, c_154, c_146, c_1206])).
% 12.17/4.76  tff(c_1228, plain, (k1_tsep_1('#skF_3', '#skF_3', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_72, c_1227])).
% 12.17/4.76  tff(c_1291, plain, (![B_363, A_364, C_365]: (m1_pre_topc(B_363, k1_tsep_1(A_364, B_363, C_365)) | ~m1_pre_topc(C_365, A_364) | v2_struct_0(C_365) | ~m1_pre_topc(B_363, A_364) | v2_struct_0(B_363) | ~l1_pre_topc(A_364) | ~v2_pre_topc(A_364) | v2_struct_0(A_364))), inference(cnfTransformation, [status(thm)], [f_116])).
% 12.17/4.76  tff(c_1320, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1228, c_1291])).
% 12.17/4.76  tff(c_1339, plain, (m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_138, c_773, c_773, c_1320])).
% 12.17/4.76  tff(c_1341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_437, c_1339])).
% 12.17/4.76  tff(c_1343, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_247])).
% 12.17/4.76  tff(c_56, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_148, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_56])).
% 12.17/4.76  tff(c_197, plain, (![B_312]: (r1_tarski(u1_struct_0(B_312), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_312, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_189])).
% 12.17/4.76  tff(c_225, plain, (![B_314]: (r1_tarski(u1_struct_0(B_314), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_314, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_197])).
% 12.17/4.76  tff(c_233, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_225])).
% 12.17/4.76  tff(c_374, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_233])).
% 12.17/4.76  tff(c_376, plain, (![B_323, A_324]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_323), u1_pre_topc(B_323)), A_324) | ~m1_pre_topc(B_323, A_324) | ~l1_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.17/4.76  tff(c_387, plain, (![A_324]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_324) | ~m1_pre_topc('#skF_3', A_324) | ~l1_pre_topc(A_324))), inference(superposition, [status(thm), theory('equality')], [c_146, c_376])).
% 12.17/4.76  tff(c_401, plain, (![A_325]: (m1_pre_topc('#skF_4', A_325) | ~m1_pre_topc('#skF_3', A_325) | ~l1_pre_topc(A_325))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_387])).
% 12.17/4.76  tff(c_405, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_401])).
% 12.17/4.76  tff(c_411, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_405])).
% 12.17/4.76  tff(c_413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_374, c_411])).
% 12.17/4.76  tff(c_414, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_233])).
% 12.17/4.76  tff(c_1342, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_247])).
% 12.17/4.76  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.17/4.76  tff(c_1362, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1342, c_2])).
% 12.17/4.76  tff(c_1365, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_1362])).
% 12.17/4.76  tff(c_1372, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1365, c_146])).
% 12.17/4.76  tff(c_52, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_50, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 12.17/4.76  tff(c_86, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50])).
% 12.17/4.76  tff(c_3207, plain, (![C_431, G_432, A_429, D_433, E_434, B_430]: (r1_tmap_1(D_433, B_430, E_434, G_432) | ~r1_tmap_1(C_431, B_430, k3_tmap_1(A_429, B_430, D_433, C_431, E_434), G_432) | ~m1_subset_1(G_432, u1_struct_0(C_431)) | ~m1_subset_1(G_432, u1_struct_0(D_433)) | ~m1_pre_topc(C_431, D_433) | ~v1_tsep_1(C_431, D_433) | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_433), u1_struct_0(B_430)))) | ~v1_funct_2(E_434, u1_struct_0(D_433), u1_struct_0(B_430)) | ~v1_funct_1(E_434) | ~m1_pre_topc(D_433, A_429) | v2_struct_0(D_433) | ~m1_pre_topc(C_431, A_429) | v2_struct_0(C_431) | ~l1_pre_topc(B_430) | ~v2_pre_topc(B_430) | v2_struct_0(B_430) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(cnfTransformation, [status(thm)], [f_218])).
% 12.17/4.76  tff(c_3209, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_3207])).
% 12.17/4.76  tff(c_3212, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_70, c_66, c_64, c_147, c_112, c_142, c_153, c_112, c_142, c_1343, c_148, c_142, c_148, c_1372, c_3209])).
% 12.17/4.76  tff(c_3213, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_72, c_68, c_48, c_3212])).
% 12.17/4.76  tff(c_178, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_172])).
% 12.17/4.76  tff(c_185, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_178])).
% 12.17/4.76  tff(c_16, plain, (![A_11]: (v3_pre_topc(k2_struct_0(A_11), A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.17/4.76  tff(c_28, plain, (![B_24, A_22]: (m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.17/4.76  tff(c_1973, plain, (![B_390, A_391]: (v1_tsep_1(B_390, A_391) | ~v3_pre_topc(u1_struct_0(B_390), A_391) | ~m1_subset_1(u1_struct_0(B_390), k1_zfmisc_1(u1_struct_0(A_391))) | ~m1_pre_topc(B_390, A_391) | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391))), inference(cnfTransformation, [status(thm)], [f_88])).
% 12.17/4.76  tff(c_4050, plain, (![B_455, A_456]: (v1_tsep_1(B_455, A_456) | ~v3_pre_topc(u1_struct_0(B_455), A_456) | ~v2_pre_topc(A_456) | ~m1_pre_topc(B_455, A_456) | ~l1_pre_topc(A_456))), inference(resolution, [status(thm)], [c_28, c_1973])).
% 12.17/4.76  tff(c_18523, plain, (![A_604]: (v1_tsep_1('#skF_3', A_604) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_604) | ~v2_pre_topc(A_604) | ~m1_pre_topc('#skF_3', A_604) | ~l1_pre_topc(A_604))), inference(superposition, [status(thm), theory('equality')], [c_1372, c_4050])).
% 12.17/4.76  tff(c_18539, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_18523])).
% 12.17/4.76  tff(c_18550, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_135, c_1343, c_18539])).
% 12.17/4.76  tff(c_18552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3213, c_18550])).
% 12.17/4.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.17/4.76  
% 12.17/4.76  Inference rules
% 12.17/4.76  ----------------------
% 12.17/4.76  #Ref     : 0
% 12.17/4.76  #Sup     : 4381
% 12.17/4.76  #Fact    : 0
% 12.17/4.76  #Define  : 0
% 12.17/4.76  #Split   : 39
% 12.17/4.76  #Chain   : 0
% 12.17/4.76  #Close   : 0
% 12.17/4.76  
% 12.17/4.76  Ordering : KBO
% 12.17/4.76  
% 12.17/4.76  Simplification rules
% 12.17/4.76  ----------------------
% 12.17/4.76  #Subsume      : 690
% 12.17/4.76  #Demod        : 7441
% 12.17/4.76  #Tautology    : 992
% 12.17/4.76  #SimpNegUnit  : 254
% 12.17/4.76  #BackRed      : 35
% 12.17/4.76  
% 12.17/4.76  #Partial instantiations: 0
% 12.17/4.76  #Strategies tried      : 1
% 12.17/4.76  
% 12.17/4.76  Timing (in seconds)
% 12.17/4.76  ----------------------
% 12.17/4.76  Preprocessing        : 0.40
% 12.17/4.76  Parsing              : 0.21
% 12.17/4.76  CNF conversion       : 0.05
% 12.17/4.77  Main loop            : 3.52
% 12.17/4.77  Inferencing          : 0.81
% 12.17/4.77  Reduction            : 1.56
% 12.17/4.77  Demodulation         : 1.24
% 12.17/4.77  BG Simplification    : 0.10
% 12.17/4.77  Subsumption          : 0.89
% 12.17/4.77  Abstraction          : 0.14
% 12.17/4.77  MUC search           : 0.00
% 12.17/4.77  Cooper               : 0.00
% 12.17/4.77  Total                : 3.97
% 12.17/4.77  Index Insertion      : 0.00
% 12.17/4.77  Index Deletion       : 0.00
% 12.17/4.77  Index Matching       : 0.00
% 12.17/4.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
