%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:35 EST 2020

% Result     : Theorem 9.14s
% Output     : CNFRefutation 9.14s
% Verified   : 
% Statistics : Number of formulae       :  160 (1268 expanded)
%              Number of leaves         :   43 ( 453 expanded)
%              Depth                    :   13
%              Number of atoms          :  400 (5843 expanded)
%              Number of equality atoms :   38 ( 671 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_257,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(f_208,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_135,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_117,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_113,plain,(
    ! [B_318,A_319] :
      ( l1_pre_topc(B_318)
      | ~ m1_pre_topc(B_318,A_319)
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_113])).

tff(c_129,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_122])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    ! [A_316] :
      ( u1_struct_0(A_316) = k2_struct_0(A_316)
      | ~ l1_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_93])).

tff(c_94,plain,(
    ! [A_317] :
      ( u1_struct_0(A_317) = k2_struct_0(A_317)
      | ~ l1_pre_topc(A_317) ) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_102,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_108,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_54])).

tff(c_148,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_108])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

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

tff(c_293,plain,(
    ! [B_327,A_328] :
      ( m1_subset_1(u1_struct_0(B_327),k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ m1_pre_topc(B_327,A_328)
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_299,plain,(
    ! [B_327] :
      ( m1_subset_1(u1_struct_0(B_327),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_327,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_293])).

tff(c_326,plain,(
    ! [B_329] :
      ( m1_subset_1(u1_struct_0(B_329),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_329,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_299])).

tff(c_332,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_326])).

tff(c_3999,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_138,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_50])).

tff(c_173,plain,(
    ! [A_323] :
      ( g1_pre_topc(u1_struct_0(A_323),u1_pre_topc(A_323)) = A_323
      | ~ v1_pre_topc(A_323)
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_173])).

tff(c_195,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_182])).

tff(c_233,plain,(
    ~ v1_pre_topc('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_234,plain,(
    ! [A_325] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_325),u1_pre_topc(A_325)))
      | ~ l1_pre_topc(A_325)
      | v2_struct_0(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_243,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_234])).

tff(c_254,plain,
    ( v1_pre_topc('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_138,c_243])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_233,c_254])).

tff(c_257,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_32,plain,(
    ! [A_59] :
      ( m1_pre_topc(A_59,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4355,plain,(
    ! [D_611,B_612,C_613,A_614] :
      ( m1_pre_topc(D_611,B_612)
      | ~ m1_pre_topc(C_613,A_614)
      | g1_pre_topc(u1_struct_0(D_611),u1_pre_topc(D_611)) != g1_pre_topc(u1_struct_0(C_613),u1_pre_topc(C_613))
      | g1_pre_topc(u1_struct_0(B_612),u1_pre_topc(B_612)) != g1_pre_topc(u1_struct_0(A_614),u1_pre_topc(A_614))
      | ~ l1_pre_topc(D_611)
      | ~ l1_pre_topc(C_613)
      | ~ l1_pre_topc(B_612)
      | ~ l1_pre_topc(A_614) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4392,plain,(
    ! [D_611,B_612,A_59] :
      ( m1_pre_topc(D_611,B_612)
      | g1_pre_topc(u1_struct_0(D_611),u1_pre_topc(D_611)) != g1_pre_topc(u1_struct_0(A_59),u1_pre_topc(A_59))
      | g1_pre_topc(u1_struct_0(B_612),u1_pre_topc(B_612)) != g1_pre_topc(u1_struct_0(A_59),u1_pre_topc(A_59))
      | ~ l1_pre_topc(D_611)
      | ~ l1_pre_topc(B_612)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_32,c_4355])).

tff(c_5500,plain,(
    ! [A_699,B_700] :
      ( m1_pre_topc(A_699,B_700)
      | g1_pre_topc(u1_struct_0(B_700),u1_pre_topc(B_700)) != g1_pre_topc(u1_struct_0(A_699),u1_pre_topc(A_699))
      | ~ l1_pre_topc(A_699)
      | ~ l1_pre_topc(B_700)
      | ~ l1_pre_topc(A_699) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4392])).

tff(c_5506,plain,(
    ! [A_699] :
      ( m1_pre_topc(A_699,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_699),u1_pre_topc(A_699)) != g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_699)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_699) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_5500])).

tff(c_5576,plain,(
    ! [A_702] :
      ( m1_pre_topc(A_702,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_702),u1_pre_topc(A_702)) != '#skF_4'
      | ~ l1_pre_topc(A_702) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_257,c_5506])).

tff(c_5585,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_5576])).

tff(c_5595,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_138,c_5585])).

tff(c_5597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3999,c_5595])).

tff(c_5599,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_149,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_48])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_139,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_77])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_6463,plain,(
    ! [D_771,G_766,E_767,B_768,C_769,A_770] :
      ( r1_tmap_1(D_771,B_768,E_767,G_766)
      | ~ r1_tmap_1(C_769,B_768,k3_tmap_1(A_770,B_768,D_771,C_769,E_767),G_766)
      | ~ m1_subset_1(G_766,u1_struct_0(C_769))
      | ~ m1_subset_1(G_766,u1_struct_0(D_771))
      | ~ m1_pre_topc(C_769,D_771)
      | ~ v1_tsep_1(C_769,D_771)
      | ~ m1_subset_1(E_767,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_771),u1_struct_0(B_768))))
      | ~ v1_funct_2(E_767,u1_struct_0(D_771),u1_struct_0(B_768))
      | ~ v1_funct_1(E_767)
      | ~ m1_pre_topc(D_771,A_770)
      | v2_struct_0(D_771)
      | ~ m1_pre_topc(C_769,A_770)
      | v2_struct_0(C_769)
      | ~ l1_pre_topc(B_768)
      | ~ v2_pre_topc(B_768)
      | v2_struct_0(B_768)
      | ~ l1_pre_topc(A_770)
      | ~ v2_pre_topc(A_770)
      | v2_struct_0(A_770) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_6465,plain,
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
    inference(resolution,[status(thm)],[c_78,c_6463])).

tff(c_6468,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_148,c_102,c_137,c_172,c_102,c_137,c_5599,c_149,c_137,c_139,c_133,c_6465])).

tff(c_6469,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_40,c_6468])).

tff(c_5598,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_155,plain,(
    ! [B_321,A_322] :
      ( v2_pre_topc(B_321)
      | ~ m1_pre_topc(B_321,A_322)
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_164,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_155])).

tff(c_171,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_164])).

tff(c_5670,plain,(
    ! [B_705,A_706] :
      ( v1_tsep_1(B_705,A_706)
      | ~ v3_pre_topc(u1_struct_0(B_705),A_706)
      | ~ m1_subset_1(u1_struct_0(B_705),k1_zfmisc_1(u1_struct_0(A_706)))
      | ~ m1_pre_topc(B_705,A_706)
      | ~ l1_pre_topc(A_706)
      | ~ v2_pre_topc(A_706) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_5679,plain,(
    ! [B_705] :
      ( v1_tsep_1(B_705,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_705),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_705),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_705,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_5670])).

tff(c_6741,plain,(
    ! [B_792] :
      ( v1_tsep_1(B_792,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_792),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_792),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_792,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_129,c_5679])).

tff(c_6753,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_6741])).

tff(c_6765,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5599,c_5598,c_133,c_6753])).

tff(c_6766,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_6469,c_6765])).

tff(c_305,plain,(
    ! [B_327] :
      ( m1_subset_1(u1_struct_0(B_327),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_327,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_293])).

tff(c_366,plain,(
    ! [B_334] :
      ( m1_subset_1(u1_struct_0(B_334),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_334,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_305])).

tff(c_372,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_366])).

tff(c_3835,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_3841,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3835])).

tff(c_3848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_3841])).

tff(c_3849,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_3850,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_161,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_155])).

tff(c_168,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_161])).

tff(c_20,plain,(
    ! [A_33] :
      ( v3_pre_topc(k2_struct_0(A_33),A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [B_58,A_56] :
      ( m1_subset_1(u1_struct_0(B_58),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_pre_topc(B_58,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_5854,plain,(
    ! [B_715,A_716] :
      ( v1_tsep_1(B_715,A_716)
      | ~ v3_pre_topc(u1_struct_0(B_715),A_716)
      | ~ v2_pre_topc(A_716)
      | ~ m1_pre_topc(B_715,A_716)
      | ~ l1_pre_topc(A_716) ) ),
    inference(resolution,[status(thm)],[c_30,c_5670])).

tff(c_5921,plain,(
    ! [A_725] :
      ( v1_tsep_1('#skF_3',A_725)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_725)
      | ~ v2_pre_topc(A_725)
      | ~ m1_pre_topc('#skF_3',A_725)
      | ~ l1_pre_topc(A_725) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_5854])).

tff(c_5928,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_5921])).

tff(c_5932,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_126,c_3850,c_5928])).

tff(c_3958,plain,(
    ! [B_581,A_582] :
      ( v3_pre_topc(u1_struct_0(B_581),A_582)
      | ~ v1_tsep_1(B_581,A_582)
      | ~ m1_subset_1(u1_struct_0(B_581),k1_zfmisc_1(u1_struct_0(A_582)))
      | ~ m1_pre_topc(B_581,A_582)
      | ~ l1_pre_topc(A_582)
      | ~ v2_pre_topc(A_582) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3973,plain,(
    ! [B_581] :
      ( v3_pre_topc(u1_struct_0(B_581),'#skF_3')
      | ~ v1_tsep_1(B_581,'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_581),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_581,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_3958])).

tff(c_11600,plain,(
    ! [B_1056] :
      ( v3_pre_topc(u1_struct_0(B_1056),'#skF_3')
      | ~ v1_tsep_1(B_1056,'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_1056),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1056,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_126,c_3973])).

tff(c_11618,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_11600])).

tff(c_11632,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3850,c_3849,c_5932,c_133,c_11618])).

tff(c_369,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_366])).

tff(c_437,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_2428,plain,(
    ! [D_481,B_482,C_483,A_484] :
      ( m1_pre_topc(D_481,B_482)
      | ~ m1_pre_topc(C_483,A_484)
      | g1_pre_topc(u1_struct_0(D_481),u1_pre_topc(D_481)) != g1_pre_topc(u1_struct_0(C_483),u1_pre_topc(C_483))
      | g1_pre_topc(u1_struct_0(B_482),u1_pre_topc(B_482)) != g1_pre_topc(u1_struct_0(A_484),u1_pre_topc(A_484))
      | ~ l1_pre_topc(D_481)
      | ~ l1_pre_topc(C_483)
      | ~ l1_pre_topc(B_482)
      | ~ l1_pre_topc(A_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2470,plain,(
    ! [D_481,B_482,A_59] :
      ( m1_pre_topc(D_481,B_482)
      | g1_pre_topc(u1_struct_0(D_481),u1_pre_topc(D_481)) != g1_pre_topc(u1_struct_0(A_59),u1_pre_topc(A_59))
      | g1_pre_topc(u1_struct_0(B_482),u1_pre_topc(B_482)) != g1_pre_topc(u1_struct_0(A_59),u1_pre_topc(A_59))
      | ~ l1_pre_topc(D_481)
      | ~ l1_pre_topc(B_482)
      | ~ l1_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_32,c_2428])).

tff(c_3621,plain,(
    ! [A_567,B_568] :
      ( m1_pre_topc(A_567,B_568)
      | g1_pre_topc(u1_struct_0(B_568),u1_pre_topc(B_568)) != g1_pre_topc(u1_struct_0(A_567),u1_pre_topc(A_567))
      | ~ l1_pre_topc(A_567)
      | ~ l1_pre_topc(B_568)
      | ~ l1_pre_topc(A_567) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2470])).

tff(c_3631,plain,(
    ! [A_567] :
      ( m1_pre_topc(A_567,'#skF_3')
      | g1_pre_topc(u1_struct_0(A_567),u1_pre_topc(A_567)) != g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_567)
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_567) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_3621])).

tff(c_3726,plain,(
    ! [A_576] :
      ( m1_pre_topc(A_576,'#skF_3')
      | g1_pre_topc(u1_struct_0(A_576),u1_pre_topc(A_576)) != '#skF_4'
      | ~ l1_pre_topc(A_576) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_138,c_3631])).

tff(c_3732,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != '#skF_4'
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_3726])).

tff(c_3743,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_257,c_3732])).

tff(c_3745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_3743])).

tff(c_3747,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_5873,plain,(
    ! [D_719,C_720,A_721] :
      ( v3_pre_topc(D_719,C_720)
      | ~ m1_subset_1(D_719,k1_zfmisc_1(u1_struct_0(C_720)))
      | ~ v3_pre_topc(D_719,A_721)
      | ~ m1_pre_topc(C_720,A_721)
      | ~ m1_subset_1(D_719,k1_zfmisc_1(u1_struct_0(A_721)))
      | ~ l1_pre_topc(A_721) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6605,plain,(
    ! [B_781,A_782,A_783] :
      ( v3_pre_topc(u1_struct_0(B_781),A_782)
      | ~ v3_pre_topc(u1_struct_0(B_781),A_783)
      | ~ m1_pre_topc(A_782,A_783)
      | ~ m1_subset_1(u1_struct_0(B_781),k1_zfmisc_1(u1_struct_0(A_783)))
      | ~ l1_pre_topc(A_783)
      | ~ m1_pre_topc(B_781,A_782)
      | ~ l1_pre_topc(A_782) ) ),
    inference(resolution,[status(thm)],[c_30,c_5873])).

tff(c_6619,plain,(
    ! [B_781] :
      ( v3_pre_topc(u1_struct_0(B_781),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_781),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_781),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_781,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3747,c_6605])).

tff(c_13158,plain,(
    ! [B_1117] :
      ( v3_pre_topc(u1_struct_0(B_1117),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_1117),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_1117),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1117,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_126,c_133,c_6619])).

tff(c_13176,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_13158])).

tff(c_13190,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5599,c_3849,c_11632,c_133,c_133,c_13176])).

tff(c_13192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6766,c_13190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.14/3.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.14/3.45  
% 9.14/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.14/3.45  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.14/3.45  
% 9.14/3.45  %Foreground sorts:
% 9.14/3.45  
% 9.14/3.45  
% 9.14/3.45  %Background operators:
% 9.14/3.45  
% 9.14/3.45  
% 9.14/3.45  %Foreground operators:
% 9.14/3.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.14/3.45  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 9.14/3.45  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.14/3.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.14/3.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.14/3.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.14/3.45  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.14/3.45  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 9.14/3.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.14/3.45  tff('#skF_7', type, '#skF_7': $i).
% 9.14/3.45  tff('#skF_5', type, '#skF_5': $i).
% 9.14/3.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.14/3.45  tff('#skF_6', type, '#skF_6': $i).
% 9.14/3.45  tff('#skF_2', type, '#skF_2': $i).
% 9.14/3.45  tff('#skF_3', type, '#skF_3': $i).
% 9.14/3.45  tff('#skF_1', type, '#skF_1': $i).
% 9.14/3.45  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.14/3.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.14/3.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.14/3.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.14/3.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.14/3.45  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 9.14/3.45  tff('#skF_4', type, '#skF_4': $i).
% 9.14/3.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.14/3.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.14/3.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.14/3.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.14/3.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.14/3.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.14/3.45  
% 9.14/3.47  tff(f_257, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 9.14/3.47  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.14/3.47  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.14/3.47  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 9.14/3.47  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.14/3.47  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 9.14/3.47  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 9.14/3.47  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.14/3.47  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 9.14/3.47  tff(f_208, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 9.14/3.47  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 9.14/3.47  tff(f_135, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 9.14/3.47  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 9.14/3.47  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 9.14/3.47  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_113, plain, (![B_318, A_319]: (l1_pre_topc(B_318) | ~m1_pre_topc(B_318, A_319) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.14/3.47  tff(c_122, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_113])).
% 9.14/3.47  tff(c_129, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_122])).
% 9.14/3.47  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.14/3.47  tff(c_89, plain, (![A_316]: (u1_struct_0(A_316)=k2_struct_0(A_316) | ~l1_struct_0(A_316))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.14/3.47  tff(c_93, plain, (![A_6]: (u1_struct_0(A_6)=k2_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_89])).
% 9.14/3.47  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_129, c_93])).
% 9.14/3.47  tff(c_94, plain, (![A_317]: (u1_struct_0(A_317)=k2_struct_0(A_317) | ~l1_pre_topc(A_317))), inference(resolution, [status(thm)], [c_8, c_89])).
% 9.14/3.47  tff(c_102, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_94])).
% 9.14/3.47  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_108, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_54])).
% 9.14/3.47  tff(c_148, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_108])).
% 9.14/3.47  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_52])).
% 9.14/3.47  tff(c_172, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 9.14/3.47  tff(c_119, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_113])).
% 9.14/3.47  tff(c_126, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_119])).
% 9.14/3.47  tff(c_133, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_126, c_93])).
% 9.14/3.47  tff(c_293, plain, (![B_327, A_328]: (m1_subset_1(u1_struct_0(B_327), k1_zfmisc_1(u1_struct_0(A_328))) | ~m1_pre_topc(B_327, A_328) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.14/3.47  tff(c_299, plain, (![B_327]: (m1_subset_1(u1_struct_0(B_327), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_327, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_293])).
% 9.14/3.47  tff(c_326, plain, (![B_329]: (m1_subset_1(u1_struct_0(B_329), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_329, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_299])).
% 9.14/3.47  tff(c_332, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_326])).
% 9.14/3.47  tff(c_3999, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_332])).
% 9.14/3.47  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_138, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_50])).
% 9.14/3.47  tff(c_173, plain, (![A_323]: (g1_pre_topc(u1_struct_0(A_323), u1_pre_topc(A_323))=A_323 | ~v1_pre_topc(A_323) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.14/3.47  tff(c_182, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_173])).
% 9.14/3.47  tff(c_195, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_182])).
% 9.14/3.47  tff(c_233, plain, (~v1_pre_topc('#skF_4')), inference(splitLeft, [status(thm)], [c_195])).
% 9.14/3.47  tff(c_234, plain, (![A_325]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_325), u1_pre_topc(A_325))) | ~l1_pre_topc(A_325) | v2_struct_0(A_325))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.14/3.47  tff(c_243, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_234])).
% 9.14/3.47  tff(c_254, plain, (v1_pre_topc('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_138, c_243])).
% 9.14/3.47  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_233, c_254])).
% 9.14/3.47  tff(c_257, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_195])).
% 9.14/3.47  tff(c_32, plain, (![A_59]: (m1_pre_topc(A_59, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.14/3.47  tff(c_4355, plain, (![D_611, B_612, C_613, A_614]: (m1_pre_topc(D_611, B_612) | ~m1_pre_topc(C_613, A_614) | g1_pre_topc(u1_struct_0(D_611), u1_pre_topc(D_611))!=g1_pre_topc(u1_struct_0(C_613), u1_pre_topc(C_613)) | g1_pre_topc(u1_struct_0(B_612), u1_pre_topc(B_612))!=g1_pre_topc(u1_struct_0(A_614), u1_pre_topc(A_614)) | ~l1_pre_topc(D_611) | ~l1_pre_topc(C_613) | ~l1_pre_topc(B_612) | ~l1_pre_topc(A_614))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.14/3.47  tff(c_4392, plain, (![D_611, B_612, A_59]: (m1_pre_topc(D_611, B_612) | g1_pre_topc(u1_struct_0(D_611), u1_pre_topc(D_611))!=g1_pre_topc(u1_struct_0(A_59), u1_pre_topc(A_59)) | g1_pre_topc(u1_struct_0(B_612), u1_pre_topc(B_612))!=g1_pre_topc(u1_struct_0(A_59), u1_pre_topc(A_59)) | ~l1_pre_topc(D_611) | ~l1_pre_topc(B_612) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_32, c_4355])).
% 9.14/3.47  tff(c_5500, plain, (![A_699, B_700]: (m1_pre_topc(A_699, B_700) | g1_pre_topc(u1_struct_0(B_700), u1_pre_topc(B_700))!=g1_pre_topc(u1_struct_0(A_699), u1_pre_topc(A_699)) | ~l1_pre_topc(A_699) | ~l1_pre_topc(B_700) | ~l1_pre_topc(A_699))), inference(reflexivity, [status(thm), theory('equality')], [c_4392])).
% 9.14/3.47  tff(c_5506, plain, (![A_699]: (m1_pre_topc(A_699, '#skF_4') | g1_pre_topc(u1_struct_0(A_699), u1_pre_topc(A_699))!=g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc(A_699) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_699))), inference(superposition, [status(thm), theory('equality')], [c_137, c_5500])).
% 9.14/3.47  tff(c_5576, plain, (![A_702]: (m1_pre_topc(A_702, '#skF_4') | g1_pre_topc(u1_struct_0(A_702), u1_pre_topc(A_702))!='#skF_4' | ~l1_pre_topc(A_702))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_257, c_5506])).
% 9.14/3.47  tff(c_5585, plain, (m1_pre_topc('#skF_3', '#skF_4') | g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_4' | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_5576])).
% 9.14/3.47  tff(c_5595, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_138, c_5585])).
% 9.14/3.47  tff(c_5597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3999, c_5595])).
% 9.14/3.47  tff(c_5599, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_332])).
% 9.14/3.47  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_149, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_48])).
% 9.14/3.47  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 9.14/3.47  tff(c_139, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_77])).
% 9.14/3.47  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_257])).
% 9.14/3.47  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 9.14/3.47  tff(c_6463, plain, (![D_771, G_766, E_767, B_768, C_769, A_770]: (r1_tmap_1(D_771, B_768, E_767, G_766) | ~r1_tmap_1(C_769, B_768, k3_tmap_1(A_770, B_768, D_771, C_769, E_767), G_766) | ~m1_subset_1(G_766, u1_struct_0(C_769)) | ~m1_subset_1(G_766, u1_struct_0(D_771)) | ~m1_pre_topc(C_769, D_771) | ~v1_tsep_1(C_769, D_771) | ~m1_subset_1(E_767, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_771), u1_struct_0(B_768)))) | ~v1_funct_2(E_767, u1_struct_0(D_771), u1_struct_0(B_768)) | ~v1_funct_1(E_767) | ~m1_pre_topc(D_771, A_770) | v2_struct_0(D_771) | ~m1_pre_topc(C_769, A_770) | v2_struct_0(C_769) | ~l1_pre_topc(B_768) | ~v2_pre_topc(B_768) | v2_struct_0(B_768) | ~l1_pre_topc(A_770) | ~v2_pre_topc(A_770) | v2_struct_0(A_770))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.14/3.47  tff(c_6465, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_6463])).
% 9.14/3.47  tff(c_6468, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_148, c_102, c_137, c_172, c_102, c_137, c_5599, c_149, c_137, c_139, c_133, c_6465])).
% 9.14/3.47  tff(c_6469, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_40, c_6468])).
% 9.14/3.47  tff(c_5598, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_332])).
% 9.14/3.47  tff(c_155, plain, (![B_321, A_322]: (v2_pre_topc(B_321) | ~m1_pre_topc(B_321, A_322) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.14/3.47  tff(c_164, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_155])).
% 9.14/3.47  tff(c_171, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_164])).
% 9.14/3.47  tff(c_5670, plain, (![B_705, A_706]: (v1_tsep_1(B_705, A_706) | ~v3_pre_topc(u1_struct_0(B_705), A_706) | ~m1_subset_1(u1_struct_0(B_705), k1_zfmisc_1(u1_struct_0(A_706))) | ~m1_pre_topc(B_705, A_706) | ~l1_pre_topc(A_706) | ~v2_pre_topc(A_706))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.14/3.47  tff(c_5679, plain, (![B_705]: (v1_tsep_1(B_705, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_705), '#skF_4') | ~m1_subset_1(u1_struct_0(B_705), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_705, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_5670])).
% 9.14/3.47  tff(c_6741, plain, (![B_792]: (v1_tsep_1(B_792, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_792), '#skF_4') | ~m1_subset_1(u1_struct_0(B_792), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_792, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_129, c_5679])).
% 9.14/3.47  tff(c_6753, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_6741])).
% 9.14/3.47  tff(c_6765, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5599, c_5598, c_133, c_6753])).
% 9.14/3.47  tff(c_6766, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_6469, c_6765])).
% 9.14/3.47  tff(c_305, plain, (![B_327]: (m1_subset_1(u1_struct_0(B_327), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_327, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_293])).
% 9.14/3.47  tff(c_366, plain, (![B_334]: (m1_subset_1(u1_struct_0(B_334), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_334, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_305])).
% 9.14/3.47  tff(c_372, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_366])).
% 9.14/3.47  tff(c_3835, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_372])).
% 9.14/3.47  tff(c_3841, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3835])).
% 9.14/3.47  tff(c_3848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_3841])).
% 9.14/3.47  tff(c_3849, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_372])).
% 9.14/3.47  tff(c_3850, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_372])).
% 9.14/3.47  tff(c_161, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_155])).
% 9.14/3.47  tff(c_168, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_161])).
% 9.14/3.47  tff(c_20, plain, (![A_33]: (v3_pre_topc(k2_struct_0(A_33), A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.14/3.47  tff(c_30, plain, (![B_58, A_56]: (m1_subset_1(u1_struct_0(B_58), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_pre_topc(B_58, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_142])).
% 9.14/3.47  tff(c_5854, plain, (![B_715, A_716]: (v1_tsep_1(B_715, A_716) | ~v3_pre_topc(u1_struct_0(B_715), A_716) | ~v2_pre_topc(A_716) | ~m1_pre_topc(B_715, A_716) | ~l1_pre_topc(A_716))), inference(resolution, [status(thm)], [c_30, c_5670])).
% 9.14/3.47  tff(c_5921, plain, (![A_725]: (v1_tsep_1('#skF_3', A_725) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_725) | ~v2_pre_topc(A_725) | ~m1_pre_topc('#skF_3', A_725) | ~l1_pre_topc(A_725))), inference(superposition, [status(thm), theory('equality')], [c_133, c_5854])).
% 9.14/3.47  tff(c_5928, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_20, c_5921])).
% 9.14/3.47  tff(c_5932, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_126, c_3850, c_5928])).
% 9.14/3.47  tff(c_3958, plain, (![B_581, A_582]: (v3_pre_topc(u1_struct_0(B_581), A_582) | ~v1_tsep_1(B_581, A_582) | ~m1_subset_1(u1_struct_0(B_581), k1_zfmisc_1(u1_struct_0(A_582))) | ~m1_pre_topc(B_581, A_582) | ~l1_pre_topc(A_582) | ~v2_pre_topc(A_582))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.14/3.47  tff(c_3973, plain, (![B_581]: (v3_pre_topc(u1_struct_0(B_581), '#skF_3') | ~v1_tsep_1(B_581, '#skF_3') | ~m1_subset_1(u1_struct_0(B_581), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_581, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_3958])).
% 9.14/3.47  tff(c_11600, plain, (![B_1056]: (v3_pre_topc(u1_struct_0(B_1056), '#skF_3') | ~v1_tsep_1(B_1056, '#skF_3') | ~m1_subset_1(u1_struct_0(B_1056), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_1056, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_126, c_3973])).
% 9.14/3.47  tff(c_11618, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_11600])).
% 9.14/3.47  tff(c_11632, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3850, c_3849, c_5932, c_133, c_11618])).
% 9.14/3.47  tff(c_369, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_137, c_366])).
% 9.14/3.47  tff(c_437, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_369])).
% 9.14/3.47  tff(c_2428, plain, (![D_481, B_482, C_483, A_484]: (m1_pre_topc(D_481, B_482) | ~m1_pre_topc(C_483, A_484) | g1_pre_topc(u1_struct_0(D_481), u1_pre_topc(D_481))!=g1_pre_topc(u1_struct_0(C_483), u1_pre_topc(C_483)) | g1_pre_topc(u1_struct_0(B_482), u1_pre_topc(B_482))!=g1_pre_topc(u1_struct_0(A_484), u1_pre_topc(A_484)) | ~l1_pre_topc(D_481) | ~l1_pre_topc(C_483) | ~l1_pre_topc(B_482) | ~l1_pre_topc(A_484))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.14/3.47  tff(c_2470, plain, (![D_481, B_482, A_59]: (m1_pre_topc(D_481, B_482) | g1_pre_topc(u1_struct_0(D_481), u1_pre_topc(D_481))!=g1_pre_topc(u1_struct_0(A_59), u1_pre_topc(A_59)) | g1_pre_topc(u1_struct_0(B_482), u1_pre_topc(B_482))!=g1_pre_topc(u1_struct_0(A_59), u1_pre_topc(A_59)) | ~l1_pre_topc(D_481) | ~l1_pre_topc(B_482) | ~l1_pre_topc(A_59))), inference(resolution, [status(thm)], [c_32, c_2428])).
% 9.14/3.47  tff(c_3621, plain, (![A_567, B_568]: (m1_pre_topc(A_567, B_568) | g1_pre_topc(u1_struct_0(B_568), u1_pre_topc(B_568))!=g1_pre_topc(u1_struct_0(A_567), u1_pre_topc(A_567)) | ~l1_pre_topc(A_567) | ~l1_pre_topc(B_568) | ~l1_pre_topc(A_567))), inference(reflexivity, [status(thm), theory('equality')], [c_2470])).
% 9.14/3.47  tff(c_3631, plain, (![A_567]: (m1_pre_topc(A_567, '#skF_3') | g1_pre_topc(u1_struct_0(A_567), u1_pre_topc(A_567))!=g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~l1_pre_topc(A_567) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_567))), inference(superposition, [status(thm), theory('equality')], [c_133, c_3621])).
% 9.14/3.47  tff(c_3726, plain, (![A_576]: (m1_pre_topc(A_576, '#skF_3') | g1_pre_topc(u1_struct_0(A_576), u1_pre_topc(A_576))!='#skF_4' | ~l1_pre_topc(A_576))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_138, c_3631])).
% 9.14/3.47  tff(c_3732, plain, (m1_pre_topc('#skF_4', '#skF_3') | g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!='#skF_4' | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_3726])).
% 9.14/3.47  tff(c_3743, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_257, c_3732])).
% 9.14/3.47  tff(c_3745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_437, c_3743])).
% 9.14/3.47  tff(c_3747, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_369])).
% 9.14/3.47  tff(c_5873, plain, (![D_719, C_720, A_721]: (v3_pre_topc(D_719, C_720) | ~m1_subset_1(D_719, k1_zfmisc_1(u1_struct_0(C_720))) | ~v3_pre_topc(D_719, A_721) | ~m1_pre_topc(C_720, A_721) | ~m1_subset_1(D_719, k1_zfmisc_1(u1_struct_0(A_721))) | ~l1_pre_topc(A_721))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.47  tff(c_6605, plain, (![B_781, A_782, A_783]: (v3_pre_topc(u1_struct_0(B_781), A_782) | ~v3_pre_topc(u1_struct_0(B_781), A_783) | ~m1_pre_topc(A_782, A_783) | ~m1_subset_1(u1_struct_0(B_781), k1_zfmisc_1(u1_struct_0(A_783))) | ~l1_pre_topc(A_783) | ~m1_pre_topc(B_781, A_782) | ~l1_pre_topc(A_782))), inference(resolution, [status(thm)], [c_30, c_5873])).
% 9.14/3.47  tff(c_6619, plain, (![B_781]: (v3_pre_topc(u1_struct_0(B_781), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_781), '#skF_3') | ~m1_subset_1(u1_struct_0(B_781), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_781, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_3747, c_6605])).
% 9.14/3.47  tff(c_13158, plain, (![B_1117]: (v3_pre_topc(u1_struct_0(B_1117), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_1117), '#skF_3') | ~m1_subset_1(u1_struct_0(B_1117), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_1117, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_126, c_133, c_6619])).
% 9.14/3.47  tff(c_13176, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_13158])).
% 9.14/3.47  tff(c_13190, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5599, c_3849, c_11632, c_133, c_133, c_13176])).
% 9.14/3.47  tff(c_13192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6766, c_13190])).
% 9.14/3.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.14/3.47  
% 9.14/3.47  Inference rules
% 9.14/3.47  ----------------------
% 9.14/3.47  #Ref     : 29
% 9.14/3.47  #Sup     : 2706
% 9.14/3.47  #Fact    : 0
% 9.14/3.47  #Define  : 0
% 9.14/3.47  #Split   : 47
% 9.14/3.48  #Chain   : 0
% 9.14/3.48  #Close   : 0
% 9.14/3.48  
% 9.14/3.48  Ordering : KBO
% 9.14/3.48  
% 9.14/3.48  Simplification rules
% 9.14/3.48  ----------------------
% 9.14/3.48  #Subsume      : 1305
% 9.14/3.48  #Demod        : 4363
% 9.14/3.48  #Tautology    : 539
% 9.14/3.48  #SimpNegUnit  : 199
% 9.14/3.48  #BackRed      : 7
% 9.14/3.48  
% 9.14/3.48  #Partial instantiations: 0
% 9.14/3.48  #Strategies tried      : 1
% 9.14/3.48  
% 9.14/3.48  Timing (in seconds)
% 9.14/3.48  ----------------------
% 9.14/3.48  Preprocessing        : 0.42
% 9.14/3.48  Parsing              : 0.23
% 9.14/3.48  CNF conversion       : 0.05
% 9.14/3.48  Main loop            : 2.22
% 9.14/3.48  Inferencing          : 0.68
% 9.14/3.48  Reduction            : 0.86
% 9.14/3.48  Demodulation         : 0.63
% 9.14/3.48  BG Simplification    : 0.06
% 9.14/3.48  Subsumption          : 0.48
% 9.14/3.48  Abstraction          : 0.08
% 9.14/3.48  MUC search           : 0.00
% 9.14/3.48  Cooper               : 0.00
% 9.14/3.48  Total                : 2.68
% 9.14/3.48  Index Insertion      : 0.00
% 9.14/3.48  Index Deletion       : 0.00
% 9.14/3.48  Index Matching       : 0.00
% 9.14/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
