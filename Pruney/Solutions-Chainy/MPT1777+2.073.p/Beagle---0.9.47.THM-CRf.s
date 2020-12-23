%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:43 EST 2020

% Result     : Theorem 40.89s
% Output     : CNFRefutation 41.03s
% Verified   : 
% Statistics : Number of formulae       :  150 (1222 expanded)
%              Number of leaves         :   44 ( 440 expanded)
%              Depth                    :   14
%              Number of atoms          :  364 (5671 expanded)
%              Number of equality atoms :   20 ( 620 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_156,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_137,axiom,(
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

tff(f_109,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_113,plain,(
    ! [B_314,A_315] :
      ( l1_pre_topc(B_314)
      | ~ m1_pre_topc(B_314,A_315)
      | ~ l1_pre_topc(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_113])).

tff(c_129,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_122])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,(
    ! [A_312] :
      ( u1_struct_0(A_312) = k2_struct_0(A_312)
      | ~ l1_struct_0(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_93])).

tff(c_94,plain,(
    ! [A_313] :
      ( u1_struct_0(A_313) = k2_struct_0(A_313)
      | ~ l1_pre_topc(A_313) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_102,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_108,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_54])).

tff(c_148,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_108])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_107,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_52])).

tff(c_172,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_107])).

tff(c_119,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_113])).

tff(c_126,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_119])).

tff(c_133,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_126,c_93])).

tff(c_208,plain,(
    ! [B_322,A_323] :
      ( m1_subset_1(u1_struct_0(B_322),k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ m1_pre_topc(B_322,A_323)
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_214,plain,(
    ! [B_322] :
      ( m1_subset_1(u1_struct_0(B_322),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_322,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_208])).

tff(c_285,plain,(
    ! [B_327] :
      ( m1_subset_1(u1_struct_0(B_327),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_327,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_214])).

tff(c_291,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_285])).

tff(c_354,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_155,plain,(
    ! [B_317,A_318] :
      ( v2_pre_topc(B_317)
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_161,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_155])).

tff(c_168,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_161])).

tff(c_32,plain,(
    ! [A_55] :
      ( m1_pre_topc(A_55,A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_220,plain,(
    ! [B_322] :
      ( m1_subset_1(u1_struct_0(B_322),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_322,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_208])).

tff(c_272,plain,(
    ! [B_326] :
      ( m1_subset_1(u1_struct_0(B_326),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_326,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_220])).

tff(c_278,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_272])).

tff(c_413,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_428,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_413])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_428])).

tff(c_434,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_138,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_50])).

tff(c_728,plain,(
    ! [A_348,B_349] :
      ( k1_tsep_1(A_348,B_349,B_349) = g1_pre_topc(u1_struct_0(B_349),u1_pre_topc(B_349))
      | ~ m1_pre_topc(B_349,A_348)
      | v2_struct_0(B_349)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348)
      | v2_struct_0(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_736,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_3','#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_434,c_728])).

tff(c_762,plain,
    ( k1_tsep_1('#skF_3','#skF_3','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_126,c_138,c_133,c_736])).

tff(c_763,plain,(
    k1_tsep_1('#skF_3','#skF_3','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_762])).

tff(c_1287,plain,(
    ! [B_361,A_362,C_363] :
      ( m1_pre_topc(B_361,k1_tsep_1(A_362,B_361,C_363))
      | ~ m1_pre_topc(C_363,A_362)
      | v2_struct_0(C_363)
      | ~ m1_pre_topc(B_361,A_362)
      | v2_struct_0(B_361)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1322,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_1287])).

tff(c_1348,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_126,c_434,c_434,c_1322])).

tff(c_1350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_354,c_1348])).

tff(c_1352,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_149,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_48])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_139,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_77])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_2737,plain,(
    ! [D_416,A_415,C_414,B_417,G_413,E_412] :
      ( r1_tmap_1(D_416,B_417,E_412,G_413)
      | ~ r1_tmap_1(C_414,B_417,k3_tmap_1(A_415,B_417,D_416,C_414,E_412),G_413)
      | ~ m1_subset_1(G_413,u1_struct_0(C_414))
      | ~ m1_subset_1(G_413,u1_struct_0(D_416))
      | ~ m1_pre_topc(C_414,D_416)
      | ~ v1_tsep_1(C_414,D_416)
      | ~ m1_subset_1(E_412,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_416),u1_struct_0(B_417))))
      | ~ v1_funct_2(E_412,u1_struct_0(D_416),u1_struct_0(B_417))
      | ~ v1_funct_1(E_412)
      | ~ m1_pre_topc(D_416,A_415)
      | v2_struct_0(D_416)
      | ~ m1_pre_topc(C_414,A_415)
      | v2_struct_0(C_414)
      | ~ l1_pre_topc(B_417)
      | ~ v2_pre_topc(B_417)
      | v2_struct_0(B_417)
      | ~ l1_pre_topc(A_415)
      | ~ v2_pre_topc(A_415)
      | v2_struct_0(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_2739,plain,
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
    inference(resolution,[status(thm)],[c_78,c_2737])).

tff(c_2742,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_148,c_102,c_137,c_172,c_102,c_137,c_1352,c_149,c_137,c_139,c_133,c_2739])).

tff(c_2743,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_40,c_2742])).

tff(c_1351,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_164,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_155])).

tff(c_171,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_164])).

tff(c_1869,plain,(
    ! [B_383,A_384] :
      ( v1_tsep_1(B_383,A_384)
      | ~ v3_pre_topc(u1_struct_0(B_383),A_384)
      | ~ m1_subset_1(u1_struct_0(B_383),k1_zfmisc_1(u1_struct_0(A_384)))
      | ~ m1_pre_topc(B_383,A_384)
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1878,plain,(
    ! [B_383] :
      ( v1_tsep_1(B_383,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_383),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_383),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_383,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_1869])).

tff(c_90763,plain,(
    ! [B_1163] :
      ( v1_tsep_1(B_1163,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_1163),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_1163),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_1163,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_129,c_1878])).

tff(c_90802,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_90763])).

tff(c_90819,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1351,c_133,c_90802])).

tff(c_90820,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_2743,c_90819])).

tff(c_1397,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_1422,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1397])).

tff(c_1426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1422])).

tff(c_1427,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_1428,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_12,plain,(
    ! [A_16] :
      ( v3_pre_topc(k2_struct_0(A_16),A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [B_44,A_42] :
      ( m1_subset_1(u1_struct_0(B_44),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_pre_topc(B_44,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3074,plain,(
    ! [B_435,A_436] :
      ( v1_tsep_1(B_435,A_436)
      | ~ v3_pre_topc(u1_struct_0(B_435),A_436)
      | ~ v2_pre_topc(A_436)
      | ~ m1_pre_topc(B_435,A_436)
      | ~ l1_pre_topc(A_436) ) ),
    inference(resolution,[status(thm)],[c_26,c_1869])).

tff(c_3217,plain,(
    ! [A_445] :
      ( v1_tsep_1('#skF_3',A_445)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_445)
      | ~ v2_pre_topc(A_445)
      | ~ m1_pre_topc('#skF_3',A_445)
      | ~ l1_pre_topc(A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_3074])).

tff(c_3221,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_3217])).

tff(c_3224,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_126,c_1428,c_3221])).

tff(c_1777,plain,(
    ! [B_380,A_381] :
      ( v3_pre_topc(u1_struct_0(B_380),A_381)
      | ~ v1_tsep_1(B_380,A_381)
      | ~ m1_subset_1(u1_struct_0(B_380),k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ m1_pre_topc(B_380,A_381)
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1792,plain,(
    ! [B_380] :
      ( v3_pre_topc(u1_struct_0(B_380),'#skF_3')
      | ~ v1_tsep_1(B_380,'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_380),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_380,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1777])).

tff(c_93608,plain,(
    ! [B_1188] :
      ( v3_pre_topc(u1_struct_0(B_1188),'#skF_3')
      | ~ v1_tsep_1(B_1188,'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_1188),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1188,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_126,c_1792])).

tff(c_93650,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_93608])).

tff(c_93668,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_1427,c_3224,c_133,c_93650])).

tff(c_298,plain,(
    ! [B_328,A_329] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_328),u1_pre_topc(B_328)),A_329)
      | ~ m1_pre_topc(B_328,A_329)
      | ~ l1_pre_topc(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_312,plain,(
    ! [A_329] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_329)
      | ~ m1_pre_topc('#skF_3',A_329)
      | ~ l1_pre_topc(A_329) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_298])).

tff(c_323,plain,(
    ! [A_330] :
      ( m1_pre_topc('#skF_4',A_330)
      | ~ m1_pre_topc('#skF_3',A_330)
      | ~ l1_pre_topc(A_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_312])).

tff(c_327,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_323])).

tff(c_333,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_327])).

tff(c_2118,plain,(
    ! [D_386,C_387,A_388] :
      ( v3_pre_topc(D_386,C_387)
      | ~ m1_subset_1(D_386,k1_zfmisc_1(u1_struct_0(C_387)))
      | ~ v3_pre_topc(D_386,A_388)
      | ~ m1_pre_topc(C_387,A_388)
      | ~ m1_subset_1(D_386,k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ l1_pre_topc(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4650,plain,(
    ! [B_477,A_478,A_479] :
      ( v3_pre_topc(u1_struct_0(B_477),A_478)
      | ~ v3_pre_topc(u1_struct_0(B_477),A_479)
      | ~ m1_pre_topc(A_478,A_479)
      | ~ m1_subset_1(u1_struct_0(B_477),k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ l1_pre_topc(A_479)
      | ~ m1_pre_topc(B_477,A_478)
      | ~ l1_pre_topc(A_478) ) ),
    inference(resolution,[status(thm)],[c_26,c_2118])).

tff(c_4698,plain,(
    ! [B_477] :
      ( v3_pre_topc(u1_struct_0(B_477),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_477),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_477),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_477,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_333,c_4650])).

tff(c_106283,plain,(
    ! [B_1268] :
      ( v3_pre_topc(u1_struct_0(B_1268),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_1268),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_1268),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1268,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_126,c_133,c_4698])).

tff(c_106328,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_106283])).

tff(c_106346,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_1427,c_93668,c_133,c_133,c_106328])).

tff(c_106348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90820,c_106346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:27:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.89/29.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.89/29.24  
% 40.89/29.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 40.89/29.24  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 40.89/29.24  
% 40.89/29.24  %Foreground sorts:
% 40.89/29.24  
% 40.89/29.24  
% 40.89/29.24  %Background operators:
% 40.89/29.24  
% 40.89/29.24  
% 40.89/29.24  %Foreground operators:
% 40.89/29.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 40.89/29.24  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 40.89/29.24  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 40.89/29.24  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 40.89/29.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 40.89/29.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 40.89/29.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.89/29.24  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 40.89/29.24  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 40.89/29.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 40.89/29.24  tff('#skF_7', type, '#skF_7': $i).
% 40.89/29.24  tff('#skF_5', type, '#skF_5': $i).
% 40.89/29.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 40.89/29.24  tff('#skF_6', type, '#skF_6': $i).
% 40.89/29.24  tff('#skF_2', type, '#skF_2': $i).
% 40.89/29.24  tff('#skF_3', type, '#skF_3': $i).
% 40.89/29.24  tff('#skF_1', type, '#skF_1': $i).
% 40.89/29.24  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 40.89/29.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 40.89/29.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 40.89/29.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.89/29.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 40.89/29.24  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 40.89/29.24  tff('#skF_4', type, '#skF_4': $i).
% 40.89/29.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.89/29.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 40.89/29.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 40.89/29.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 40.89/29.24  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 40.89/29.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 40.89/29.24  
% 41.03/29.27  tff(f_267, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 41.03/29.27  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 41.03/29.27  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 41.03/29.27  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 41.03/29.27  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 41.03/29.27  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 41.03/29.27  tff(f_156, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 41.03/29.27  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 41.03/29.27  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 41.03/29.27  tff(f_218, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 41.03/29.27  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 41.03/29.27  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 41.03/29.27  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 41.03/29.27  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 41.03/29.27  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_113, plain, (![B_314, A_315]: (l1_pre_topc(B_314) | ~m1_pre_topc(B_314, A_315) | ~l1_pre_topc(A_315))), inference(cnfTransformation, [status(thm)], [f_49])).
% 41.03/29.27  tff(c_122, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_113])).
% 41.03/29.27  tff(c_129, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_122])).
% 41.03/29.27  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 41.03/29.27  tff(c_89, plain, (![A_312]: (u1_struct_0(A_312)=k2_struct_0(A_312) | ~l1_struct_0(A_312))), inference(cnfTransformation, [status(thm)], [f_38])).
% 41.03/29.27  tff(c_93, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_89])).
% 41.03/29.27  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_129, c_93])).
% 41.03/29.27  tff(c_94, plain, (![A_313]: (u1_struct_0(A_313)=k2_struct_0(A_313) | ~l1_pre_topc(A_313))), inference(resolution, [status(thm)], [c_6, c_89])).
% 41.03/29.27  tff(c_102, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_94])).
% 41.03/29.27  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_108, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_54])).
% 41.03/29.27  tff(c_148, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_108])).
% 41.03/29.27  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_52])).
% 41.03/29.27  tff(c_172, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 41.03/29.27  tff(c_119, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_113])).
% 41.03/29.27  tff(c_126, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_119])).
% 41.03/29.27  tff(c_133, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_126, c_93])).
% 41.03/29.27  tff(c_208, plain, (![B_322, A_323]: (m1_subset_1(u1_struct_0(B_322), k1_zfmisc_1(u1_struct_0(A_323))) | ~m1_pre_topc(B_322, A_323) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_116])).
% 41.03/29.27  tff(c_214, plain, (![B_322]: (m1_subset_1(u1_struct_0(B_322), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_322, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_208])).
% 41.03/29.27  tff(c_285, plain, (![B_327]: (m1_subset_1(u1_struct_0(B_327), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_327, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_214])).
% 41.03/29.27  tff(c_291, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_285])).
% 41.03/29.27  tff(c_354, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_291])).
% 41.03/29.27  tff(c_155, plain, (![B_317, A_318]: (v2_pre_topc(B_317) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_34])).
% 41.03/29.27  tff(c_161, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_155])).
% 41.03/29.27  tff(c_168, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_161])).
% 41.03/29.27  tff(c_32, plain, (![A_55]: (m1_pre_topc(A_55, A_55) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_156])).
% 41.03/29.27  tff(c_220, plain, (![B_322]: (m1_subset_1(u1_struct_0(B_322), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_322, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_208])).
% 41.03/29.27  tff(c_272, plain, (![B_326]: (m1_subset_1(u1_struct_0(B_326), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_326, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_220])).
% 41.03/29.27  tff(c_278, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_272])).
% 41.03/29.27  tff(c_413, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_278])).
% 41.03/29.27  tff(c_428, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_413])).
% 41.03/29.27  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_428])).
% 41.03/29.27  tff(c_434, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_278])).
% 41.03/29.27  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_138, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_50])).
% 41.03/29.27  tff(c_728, plain, (![A_348, B_349]: (k1_tsep_1(A_348, B_349, B_349)=g1_pre_topc(u1_struct_0(B_349), u1_pre_topc(B_349)) | ~m1_pre_topc(B_349, A_348) | v2_struct_0(B_349) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348) | v2_struct_0(A_348))), inference(cnfTransformation, [status(thm)], [f_152])).
% 41.03/29.27  tff(c_736, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_3', '#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_434, c_728])).
% 41.03/29.27  tff(c_762, plain, (k1_tsep_1('#skF_3', '#skF_3', '#skF_3')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_126, c_138, c_133, c_736])).
% 41.03/29.27  tff(c_763, plain, (k1_tsep_1('#skF_3', '#skF_3', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_64, c_762])).
% 41.03/29.27  tff(c_1287, plain, (![B_361, A_362, C_363]: (m1_pre_topc(B_361, k1_tsep_1(A_362, B_361, C_363)) | ~m1_pre_topc(C_363, A_362) | v2_struct_0(C_363) | ~m1_pre_topc(B_361, A_362) | v2_struct_0(B_361) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(cnfTransformation, [status(thm)], [f_137])).
% 41.03/29.27  tff(c_1322, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_763, c_1287])).
% 41.03/29.27  tff(c_1348, plain, (m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_126, c_434, c_434, c_1322])).
% 41.03/29.27  tff(c_1350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_354, c_1348])).
% 41.03/29.27  tff(c_1352, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_291])).
% 41.03/29.27  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_149, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_48])).
% 41.03/29.27  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 41.03/29.27  tff(c_139, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_77])).
% 41.03/29.27  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_267])).
% 41.03/29.27  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 41.03/29.27  tff(c_2737, plain, (![D_416, A_415, C_414, B_417, G_413, E_412]: (r1_tmap_1(D_416, B_417, E_412, G_413) | ~r1_tmap_1(C_414, B_417, k3_tmap_1(A_415, B_417, D_416, C_414, E_412), G_413) | ~m1_subset_1(G_413, u1_struct_0(C_414)) | ~m1_subset_1(G_413, u1_struct_0(D_416)) | ~m1_pre_topc(C_414, D_416) | ~v1_tsep_1(C_414, D_416) | ~m1_subset_1(E_412, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_416), u1_struct_0(B_417)))) | ~v1_funct_2(E_412, u1_struct_0(D_416), u1_struct_0(B_417)) | ~v1_funct_1(E_412) | ~m1_pre_topc(D_416, A_415) | v2_struct_0(D_416) | ~m1_pre_topc(C_414, A_415) | v2_struct_0(C_414) | ~l1_pre_topc(B_417) | ~v2_pre_topc(B_417) | v2_struct_0(B_417) | ~l1_pre_topc(A_415) | ~v2_pre_topc(A_415) | v2_struct_0(A_415))), inference(cnfTransformation, [status(thm)], [f_218])).
% 41.03/29.27  tff(c_2739, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_2737])).
% 41.03/29.27  tff(c_2742, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_148, c_102, c_137, c_172, c_102, c_137, c_1352, c_149, c_137, c_139, c_133, c_2739])).
% 41.03/29.27  tff(c_2743, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_40, c_2742])).
% 41.03/29.27  tff(c_1351, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_291])).
% 41.03/29.27  tff(c_164, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_155])).
% 41.03/29.27  tff(c_171, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_164])).
% 41.03/29.27  tff(c_1869, plain, (![B_383, A_384]: (v1_tsep_1(B_383, A_384) | ~v3_pre_topc(u1_struct_0(B_383), A_384) | ~m1_subset_1(u1_struct_0(B_383), k1_zfmisc_1(u1_struct_0(A_384))) | ~m1_pre_topc(B_383, A_384) | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384))), inference(cnfTransformation, [status(thm)], [f_109])).
% 41.03/29.27  tff(c_1878, plain, (![B_383]: (v1_tsep_1(B_383, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_383), '#skF_4') | ~m1_subset_1(u1_struct_0(B_383), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_383, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_1869])).
% 41.03/29.27  tff(c_90763, plain, (![B_1163]: (v1_tsep_1(B_1163, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_1163), '#skF_4') | ~m1_subset_1(u1_struct_0(B_1163), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_1163, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_129, c_1878])).
% 41.03/29.27  tff(c_90802, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_90763])).
% 41.03/29.27  tff(c_90819, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1351, c_133, c_90802])).
% 41.03/29.27  tff(c_90820, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_2743, c_90819])).
% 41.03/29.27  tff(c_1397, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_278])).
% 41.03/29.27  tff(c_1422, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1397])).
% 41.03/29.27  tff(c_1426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_1422])).
% 41.03/29.27  tff(c_1427, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_278])).
% 41.03/29.27  tff(c_1428, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_278])).
% 41.03/29.27  tff(c_12, plain, (![A_16]: (v3_pre_topc(k2_struct_0(A_16), A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 41.03/29.27  tff(c_26, plain, (![B_44, A_42]: (m1_subset_1(u1_struct_0(B_44), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_pre_topc(B_44, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 41.03/29.27  tff(c_3074, plain, (![B_435, A_436]: (v1_tsep_1(B_435, A_436) | ~v3_pre_topc(u1_struct_0(B_435), A_436) | ~v2_pre_topc(A_436) | ~m1_pre_topc(B_435, A_436) | ~l1_pre_topc(A_436))), inference(resolution, [status(thm)], [c_26, c_1869])).
% 41.03/29.27  tff(c_3217, plain, (![A_445]: (v1_tsep_1('#skF_3', A_445) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_445) | ~v2_pre_topc(A_445) | ~m1_pre_topc('#skF_3', A_445) | ~l1_pre_topc(A_445))), inference(superposition, [status(thm), theory('equality')], [c_133, c_3074])).
% 41.03/29.27  tff(c_3221, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_3217])).
% 41.03/29.27  tff(c_3224, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_126, c_1428, c_3221])).
% 41.03/29.27  tff(c_1777, plain, (![B_380, A_381]: (v3_pre_topc(u1_struct_0(B_380), A_381) | ~v1_tsep_1(B_380, A_381) | ~m1_subset_1(u1_struct_0(B_380), k1_zfmisc_1(u1_struct_0(A_381))) | ~m1_pre_topc(B_380, A_381) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381))), inference(cnfTransformation, [status(thm)], [f_109])).
% 41.03/29.27  tff(c_1792, plain, (![B_380]: (v3_pre_topc(u1_struct_0(B_380), '#skF_3') | ~v1_tsep_1(B_380, '#skF_3') | ~m1_subset_1(u1_struct_0(B_380), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_380, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1777])).
% 41.03/29.27  tff(c_93608, plain, (![B_1188]: (v3_pre_topc(u1_struct_0(B_1188), '#skF_3') | ~v1_tsep_1(B_1188, '#skF_3') | ~m1_subset_1(u1_struct_0(B_1188), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_1188, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_126, c_1792])).
% 41.03/29.27  tff(c_93650, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_93608])).
% 41.03/29.27  tff(c_93668, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_1427, c_3224, c_133, c_93650])).
% 41.03/29.27  tff(c_298, plain, (![B_328, A_329]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_328), u1_pre_topc(B_328)), A_329) | ~m1_pre_topc(B_328, A_329) | ~l1_pre_topc(A_329))), inference(cnfTransformation, [status(thm)], [f_91])).
% 41.03/29.27  tff(c_312, plain, (![A_329]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_329) | ~m1_pre_topc('#skF_3', A_329) | ~l1_pre_topc(A_329))), inference(superposition, [status(thm), theory('equality')], [c_133, c_298])).
% 41.03/29.27  tff(c_323, plain, (![A_330]: (m1_pre_topc('#skF_4', A_330) | ~m1_pre_topc('#skF_3', A_330) | ~l1_pre_topc(A_330))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_312])).
% 41.03/29.27  tff(c_327, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_323])).
% 41.03/29.27  tff(c_333, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_327])).
% 41.03/29.27  tff(c_2118, plain, (![D_386, C_387, A_388]: (v3_pre_topc(D_386, C_387) | ~m1_subset_1(D_386, k1_zfmisc_1(u1_struct_0(C_387))) | ~v3_pre_topc(D_386, A_388) | ~m1_pre_topc(C_387, A_388) | ~m1_subset_1(D_386, k1_zfmisc_1(u1_struct_0(A_388))) | ~l1_pre_topc(A_388))), inference(cnfTransformation, [status(thm)], [f_82])).
% 41.03/29.27  tff(c_4650, plain, (![B_477, A_478, A_479]: (v3_pre_topc(u1_struct_0(B_477), A_478) | ~v3_pre_topc(u1_struct_0(B_477), A_479) | ~m1_pre_topc(A_478, A_479) | ~m1_subset_1(u1_struct_0(B_477), k1_zfmisc_1(u1_struct_0(A_479))) | ~l1_pre_topc(A_479) | ~m1_pre_topc(B_477, A_478) | ~l1_pre_topc(A_478))), inference(resolution, [status(thm)], [c_26, c_2118])).
% 41.03/29.27  tff(c_4698, plain, (![B_477]: (v3_pre_topc(u1_struct_0(B_477), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_477), '#skF_3') | ~m1_subset_1(u1_struct_0(B_477), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_477, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_333, c_4650])).
% 41.03/29.27  tff(c_106283, plain, (![B_1268]: (v3_pre_topc(u1_struct_0(B_1268), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_1268), '#skF_3') | ~m1_subset_1(u1_struct_0(B_1268), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_1268, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_126, c_133, c_4698])).
% 41.03/29.27  tff(c_106328, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_106283])).
% 41.03/29.27  tff(c_106346, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_1427, c_93668, c_133, c_133, c_106328])).
% 41.03/29.27  tff(c_106348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90820, c_106346])).
% 41.03/29.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 41.03/29.27  
% 41.03/29.27  Inference rules
% 41.03/29.27  ----------------------
% 41.03/29.27  #Ref     : 0
% 41.03/29.27  #Sup     : 27608
% 41.03/29.27  #Fact    : 0
% 41.03/29.27  #Define  : 0
% 41.03/29.27  #Split   : 75
% 41.03/29.27  #Chain   : 0
% 41.03/29.27  #Close   : 0
% 41.03/29.27  
% 41.03/29.27  Ordering : KBO
% 41.03/29.27  
% 41.03/29.27  Simplification rules
% 41.03/29.27  ----------------------
% 41.03/29.27  #Subsume      : 3801
% 41.03/29.27  #Demod        : 35242
% 41.03/29.27  #Tautology    : 4623
% 41.03/29.27  #SimpNegUnit  : 1543
% 41.03/29.27  #BackRed      : 25
% 41.03/29.27  
% 41.03/29.27  #Partial instantiations: 0
% 41.03/29.27  #Strategies tried      : 1
% 41.03/29.27  
% 41.03/29.27  Timing (in seconds)
% 41.03/29.27  ----------------------
% 41.03/29.27  Preprocessing        : 0.37
% 41.03/29.27  Parsing              : 0.19
% 41.03/29.27  CNF conversion       : 0.05
% 41.03/29.27  Main loop            : 28.17
% 41.03/29.27  Inferencing          : 4.29
% 41.03/29.27  Reduction            : 11.88
% 41.03/29.27  Demodulation         : 9.94
% 41.03/29.27  BG Simplification    : 0.73
% 41.03/29.27  Subsumption          : 10.23
% 41.03/29.27  Abstraction          : 1.07
% 41.03/29.27  MUC search           : 0.00
% 41.03/29.27  Cooper               : 0.00
% 41.03/29.27  Total                : 28.59
% 41.03/29.27  Index Insertion      : 0.00
% 41.03/29.27  Index Deletion       : 0.00
% 41.03/29.27  Index Matching       : 0.00
% 41.03/29.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
