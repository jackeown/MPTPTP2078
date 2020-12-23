%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:34 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  134 (1207 expanded)
%              Number of leaves         :   44 ( 428 expanded)
%              Depth                    :   16
%              Number of atoms          :  285 (5454 expanded)
%              Number of equality atoms :   38 ( 731 expanded)
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

tff(f_233,negated_conjecture,(
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

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_184,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_111,axiom,(
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

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_117,plain,(
    ! [B_291,A_292] :
      ( l1_pre_topc(B_291)
      | ~ m1_pre_topc(B_291,A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_130,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_123])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [A_289] :
      ( u1_struct_0(A_289) = k2_struct_0(A_289)
      | ~ l1_struct_0(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_97])).

tff(c_98,plain,(
    ! [A_290] :
      ( u1_struct_0(A_290) = k2_struct_0(A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_105,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_98])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_108,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58])).

tff(c_142,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_108])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_107,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_56])).

tff(c_180,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_107])).

tff(c_126,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_117])).

tff(c_133,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_126])).

tff(c_36,plain,(
    ! [A_32] :
      ( m1_pre_topc(A_32,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_141,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_316,plain,(
    ! [B_301,A_302] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ m1_pre_topc(B_301,A_302)
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_322,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_301,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_316])).

tff(c_349,plain,(
    ! [B_303] :
      ( m1_subset_1(u1_struct_0(B_303),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_303,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_322])).

tff(c_352,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_349])).

tff(c_448,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_451,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_448])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_451])).

tff(c_457,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_223,plain,(
    ! [A_298] :
      ( g1_pre_topc(u1_struct_0(A_298),u1_pre_topc(A_298)) = A_298
      | ~ v1_pre_topc(A_298)
      | ~ l1_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_238,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_223])).

tff(c_250,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_238])).

tff(c_256,plain,(
    ~ v1_pre_topc('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_148,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_54])).

tff(c_259,plain,(
    ! [A_299] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_299),u1_pre_topc(A_299)))
      | ~ l1_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_265,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_259])).

tff(c_276,plain,
    ( v1_pre_topc('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_148,c_265])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_256,c_276])).

tff(c_279,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_159,plain,(
    ! [A_294] :
      ( m1_subset_1(u1_pre_topc(A_294),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_294))))
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_159])).

tff(c_173,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_162])).

tff(c_477,plain,(
    ! [C_311,A_312,D_313,B_314] :
      ( C_311 = A_312
      | g1_pre_topc(C_311,D_313) != g1_pre_topc(A_312,B_314)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(k1_zfmisc_1(A_312))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_489,plain,(
    ! [C_311,D_313] :
      ( k2_struct_0('#skF_3') = C_311
      | g1_pre_topc(C_311,D_313) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_477])).

tff(c_494,plain,(
    ! [C_315,D_316] :
      ( k2_struct_0('#skF_3') = C_315
      | g1_pre_topc(C_315,D_316) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_489])).

tff(c_504,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_494])).

tff(c_512,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_148])).

tff(c_165,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_159])).

tff(c_175,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_165])).

tff(c_598,plain,(
    ! [D_318,B_319,C_320,A_321] :
      ( D_318 = B_319
      | g1_pre_topc(C_320,D_318) != g1_pre_topc(A_321,B_319)
      | ~ m1_subset_1(B_319,k1_zfmisc_1(k1_zfmisc_1(A_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_606,plain,(
    ! [D_318,C_320] :
      ( u1_pre_topc('#skF_4') = D_318
      | g1_pre_topc(C_320,D_318) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_598])).

tff(c_629,plain,(
    ! [D_324,C_325] :
      ( u1_pre_topc('#skF_4') = D_324
      | g1_pre_topc(C_325,D_324) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_606])).

tff(c_639,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_629])).

tff(c_514,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_141])).

tff(c_847,plain,(
    ! [A_332,B_333] :
      ( m1_pre_topc(A_332,g1_pre_topc(u1_struct_0(B_333),u1_pre_topc(B_333)))
      | ~ m1_pre_topc(A_332,B_333)
      | ~ l1_pre_topc(B_333)
      | ~ l1_pre_topc(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_868,plain,(
    ! [A_332] :
      ( m1_pre_topc(A_332,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_332,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_332) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_847])).

tff(c_898,plain,(
    ! [A_334] :
      ( m1_pre_topc(A_334,'#skF_4')
      | ~ m1_pre_topc(A_334,'#skF_3')
      | ~ l1_pre_topc(A_334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_279,c_639,c_868])).

tff(c_908,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_457,c_898])).

tff(c_919,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_908])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_143,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_52])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1377,plain,(
    ! [C_367,D_366,G_365,A_362,E_363,B_364] :
      ( r1_tmap_1(D_366,B_364,E_363,G_365)
      | ~ r1_tmap_1(C_367,B_364,k3_tmap_1(A_362,B_364,D_366,C_367,E_363),G_365)
      | ~ m1_subset_1(G_365,u1_struct_0(C_367))
      | ~ m1_subset_1(G_365,u1_struct_0(D_366))
      | ~ m1_pre_topc(C_367,D_366)
      | ~ v1_tsep_1(C_367,D_366)
      | ~ m1_subset_1(E_363,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_366),u1_struct_0(B_364))))
      | ~ v1_funct_2(E_363,u1_struct_0(D_366),u1_struct_0(B_364))
      | ~ v1_funct_1(E_363)
      | ~ m1_pre_topc(D_366,A_362)
      | v2_struct_0(D_366)
      | ~ m1_pre_topc(C_367,A_362)
      | v2_struct_0(C_367)
      | ~ l1_pre_topc(B_364)
      | ~ v2_pre_topc(B_364)
      | v2_struct_0(B_364)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1379,plain,
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
    inference(resolution,[status(thm)],[c_82,c_1377])).

tff(c_1382,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_142,c_105,c_137,c_180,c_105,c_137,c_919,c_143,c_137,c_143,c_514,c_1379])).

tff(c_1383,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_1382])).

tff(c_181,plain,(
    ! [B_295,A_296] :
      ( v2_pre_topc(B_295)
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_187,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_181])).

tff(c_194,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_187])).

tff(c_26,plain,(
    ! [A_21] :
      ( v3_pre_topc(k2_struct_0(A_21),A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    ! [B_31,A_29] :
      ( m1_subset_1(u1_struct_0(B_31),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_pre_topc(B_31,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_962,plain,(
    ! [B_335,A_336] :
      ( v1_tsep_1(B_335,A_336)
      | ~ v3_pre_topc(u1_struct_0(B_335),A_336)
      | ~ m1_subset_1(u1_struct_0(B_335),k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ m1_pre_topc(B_335,A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1386,plain,(
    ! [B_372,A_373] :
      ( v1_tsep_1(B_372,A_373)
      | ~ v3_pre_topc(u1_struct_0(B_372),A_373)
      | ~ v2_pre_topc(A_373)
      | ~ m1_pre_topc(B_372,A_373)
      | ~ l1_pre_topc(A_373) ) ),
    inference(resolution,[status(thm)],[c_34,c_962])).

tff(c_1754,plain,(
    ! [A_396] :
      ( v1_tsep_1('#skF_3',A_396)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_396)
      | ~ v2_pre_topc(A_396)
      | ~ m1_pre_topc('#skF_3',A_396)
      | ~ l1_pre_topc(A_396) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_1386])).

tff(c_1764,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1754])).

tff(c_1771,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_130,c_919,c_1764])).

tff(c_1773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1383,c_1771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.87  
% 4.90/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.87  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.90/1.87  
% 4.90/1.87  %Foreground sorts:
% 4.90/1.87  
% 4.90/1.87  
% 4.90/1.87  %Background operators:
% 4.90/1.87  
% 4.90/1.87  
% 4.90/1.87  %Foreground operators:
% 4.90/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.90/1.87  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.90/1.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.90/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.90/1.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.90/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.90/1.87  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.90/1.87  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.90/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.90/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.90/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.90/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.90/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.90/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.90/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.90/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.90/1.87  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.90/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.90/1.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.90/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.90/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.90/1.87  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.90/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.90/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.90/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.90/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.90/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.90/1.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.90/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.90/1.87  
% 4.90/1.90  tff(f_233, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.90/1.90  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.90/1.90  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.90/1.90  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.90/1.90  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.90/1.90  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.90/1.90  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.90/1.90  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_pre_topc)).
% 4.90/1.90  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.90/1.90  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.90/1.90  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.90/1.90  tff(f_184, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.90/1.90  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.90/1.90  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.90/1.90  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.90/1.90  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_117, plain, (![B_291, A_292]: (l1_pre_topc(B_291) | ~m1_pre_topc(B_291, A_292) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.90/1.90  tff(c_123, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_117])).
% 4.90/1.90  tff(c_130, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_123])).
% 4.90/1.90  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.90/1.90  tff(c_93, plain, (![A_289]: (u1_struct_0(A_289)=k2_struct_0(A_289) | ~l1_struct_0(A_289))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.90/1.90  tff(c_97, plain, (![A_6]: (u1_struct_0(A_6)=k2_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_93])).
% 4.90/1.90  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_97])).
% 4.90/1.90  tff(c_98, plain, (![A_290]: (u1_struct_0(A_290)=k2_struct_0(A_290) | ~l1_pre_topc(A_290))), inference(resolution, [status(thm)], [c_8, c_93])).
% 4.90/1.90  tff(c_105, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_98])).
% 4.90/1.90  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_108, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58])).
% 4.90/1.90  tff(c_142, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_108])).
% 4.90/1.90  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_56])).
% 4.90/1.90  tff(c_180, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 4.90/1.90  tff(c_126, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_117])).
% 4.90/1.90  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126])).
% 4.90/1.90  tff(c_36, plain, (![A_32]: (m1_pre_topc(A_32, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.90/1.90  tff(c_141, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_97])).
% 4.90/1.90  tff(c_316, plain, (![B_301, A_302]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(u1_struct_0(A_302))) | ~m1_pre_topc(B_301, A_302) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.90/1.90  tff(c_322, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_301, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_316])).
% 4.90/1.90  tff(c_349, plain, (![B_303]: (m1_subset_1(u1_struct_0(B_303), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_303, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_322])).
% 4.90/1.90  tff(c_352, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_349])).
% 4.90/1.90  tff(c_448, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_352])).
% 4.90/1.90  tff(c_451, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_448])).
% 4.90/1.90  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_451])).
% 4.90/1.90  tff(c_457, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_352])).
% 4.90/1.90  tff(c_223, plain, (![A_298]: (g1_pre_topc(u1_struct_0(A_298), u1_pre_topc(A_298))=A_298 | ~v1_pre_topc(A_298) | ~l1_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.90/1.90  tff(c_238, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_223])).
% 4.90/1.90  tff(c_250, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_238])).
% 4.90/1.90  tff(c_256, plain, (~v1_pre_topc('#skF_4')), inference(splitLeft, [status(thm)], [c_250])).
% 4.90/1.90  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_148, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_54])).
% 4.90/1.90  tff(c_259, plain, (![A_299]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_299), u1_pre_topc(A_299))) | ~l1_pre_topc(A_299) | v2_struct_0(A_299))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.90/1.90  tff(c_265, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_259])).
% 4.90/1.90  tff(c_276, plain, (v1_pre_topc('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_148, c_265])).
% 4.90/1.90  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_256, c_276])).
% 4.90/1.90  tff(c_279, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_250])).
% 4.90/1.90  tff(c_159, plain, (![A_294]: (m1_subset_1(u1_pre_topc(A_294), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_294)))) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.90/1.90  tff(c_162, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_159])).
% 4.90/1.90  tff(c_173, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_162])).
% 4.90/1.90  tff(c_477, plain, (![C_311, A_312, D_313, B_314]: (C_311=A_312 | g1_pre_topc(C_311, D_313)!=g1_pre_topc(A_312, B_314) | ~m1_subset_1(B_314, k1_zfmisc_1(k1_zfmisc_1(A_312))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.90/1.90  tff(c_489, plain, (![C_311, D_313]: (k2_struct_0('#skF_3')=C_311 | g1_pre_topc(C_311, D_313)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_148, c_477])).
% 4.90/1.90  tff(c_494, plain, (![C_315, D_316]: (k2_struct_0('#skF_3')=C_315 | g1_pre_topc(C_315, D_316)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_489])).
% 4.90/1.90  tff(c_504, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_279, c_494])).
% 4.90/1.90  tff(c_512, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_504, c_148])).
% 4.90/1.90  tff(c_165, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_159])).
% 4.90/1.90  tff(c_175, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_165])).
% 4.90/1.90  tff(c_598, plain, (![D_318, B_319, C_320, A_321]: (D_318=B_319 | g1_pre_topc(C_320, D_318)!=g1_pre_topc(A_321, B_319) | ~m1_subset_1(B_319, k1_zfmisc_1(k1_zfmisc_1(A_321))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.90/1.90  tff(c_606, plain, (![D_318, C_320]: (u1_pre_topc('#skF_4')=D_318 | g1_pre_topc(C_320, D_318)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_279, c_598])).
% 4.90/1.90  tff(c_629, plain, (![D_324, C_325]: (u1_pre_topc('#skF_4')=D_324 | g1_pre_topc(C_325, D_324)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_606])).
% 4.90/1.90  tff(c_639, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_512, c_629])).
% 4.90/1.90  tff(c_514, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_141])).
% 4.90/1.90  tff(c_847, plain, (![A_332, B_333]: (m1_pre_topc(A_332, g1_pre_topc(u1_struct_0(B_333), u1_pre_topc(B_333))) | ~m1_pre_topc(A_332, B_333) | ~l1_pre_topc(B_333) | ~l1_pre_topc(A_332))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.90/1.90  tff(c_868, plain, (![A_332]: (m1_pre_topc(A_332, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_332, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_332))), inference(superposition, [status(thm), theory('equality')], [c_514, c_847])).
% 4.90/1.90  tff(c_898, plain, (![A_334]: (m1_pre_topc(A_334, '#skF_4') | ~m1_pre_topc(A_334, '#skF_3') | ~l1_pre_topc(A_334))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_279, c_639, c_868])).
% 4.90/1.90  tff(c_908, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_457, c_898])).
% 4.90/1.90  tff(c_919, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_908])).
% 4.90/1.90  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_143, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_52])).
% 4.90/1.90  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_233])).
% 4.90/1.90  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 4.90/1.90  tff(c_1377, plain, (![C_367, D_366, G_365, A_362, E_363, B_364]: (r1_tmap_1(D_366, B_364, E_363, G_365) | ~r1_tmap_1(C_367, B_364, k3_tmap_1(A_362, B_364, D_366, C_367, E_363), G_365) | ~m1_subset_1(G_365, u1_struct_0(C_367)) | ~m1_subset_1(G_365, u1_struct_0(D_366)) | ~m1_pre_topc(C_367, D_366) | ~v1_tsep_1(C_367, D_366) | ~m1_subset_1(E_363, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_366), u1_struct_0(B_364)))) | ~v1_funct_2(E_363, u1_struct_0(D_366), u1_struct_0(B_364)) | ~v1_funct_1(E_363) | ~m1_pre_topc(D_366, A_362) | v2_struct_0(D_366) | ~m1_pre_topc(C_367, A_362) | v2_struct_0(C_367) | ~l1_pre_topc(B_364) | ~v2_pre_topc(B_364) | v2_struct_0(B_364) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362) | v2_struct_0(A_362))), inference(cnfTransformation, [status(thm)], [f_184])).
% 4.90/1.90  tff(c_1379, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_1377])).
% 4.90/1.90  tff(c_1382, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_142, c_105, c_137, c_180, c_105, c_137, c_919, c_143, c_137, c_143, c_514, c_1379])).
% 4.90/1.90  tff(c_1383, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_1382])).
% 4.90/1.90  tff(c_181, plain, (![B_295, A_296]: (v2_pre_topc(B_295) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.90/1.90  tff(c_187, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_181])).
% 4.90/1.90  tff(c_194, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_187])).
% 4.90/1.90  tff(c_26, plain, (![A_21]: (v3_pre_topc(k2_struct_0(A_21), A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.90/1.90  tff(c_34, plain, (![B_31, A_29]: (m1_subset_1(u1_struct_0(B_31), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_pre_topc(B_31, A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.90/1.90  tff(c_962, plain, (![B_335, A_336]: (v1_tsep_1(B_335, A_336) | ~v3_pre_topc(u1_struct_0(B_335), A_336) | ~m1_subset_1(u1_struct_0(B_335), k1_zfmisc_1(u1_struct_0(A_336))) | ~m1_pre_topc(B_335, A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.90/1.90  tff(c_1386, plain, (![B_372, A_373]: (v1_tsep_1(B_372, A_373) | ~v3_pre_topc(u1_struct_0(B_372), A_373) | ~v2_pre_topc(A_373) | ~m1_pre_topc(B_372, A_373) | ~l1_pre_topc(A_373))), inference(resolution, [status(thm)], [c_34, c_962])).
% 4.90/1.90  tff(c_1754, plain, (![A_396]: (v1_tsep_1('#skF_3', A_396) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_396) | ~v2_pre_topc(A_396) | ~m1_pre_topc('#skF_3', A_396) | ~l1_pre_topc(A_396))), inference(superposition, [status(thm), theory('equality')], [c_514, c_1386])).
% 4.90/1.90  tff(c_1764, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1754])).
% 4.90/1.90  tff(c_1771, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_130, c_919, c_1764])).
% 4.90/1.90  tff(c_1773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1383, c_1771])).
% 4.90/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.90  
% 4.90/1.90  Inference rules
% 4.90/1.90  ----------------------
% 4.90/1.90  #Ref     : 3
% 4.90/1.90  #Sup     : 342
% 4.90/1.90  #Fact    : 0
% 4.90/1.90  #Define  : 0
% 4.90/1.90  #Split   : 21
% 4.90/1.90  #Chain   : 0
% 4.90/1.90  #Close   : 0
% 4.90/1.90  
% 4.90/1.90  Ordering : KBO
% 4.90/1.90  
% 4.90/1.90  Simplification rules
% 4.90/1.90  ----------------------
% 4.90/1.90  #Subsume      : 54
% 4.90/1.90  #Demod        : 461
% 4.90/1.90  #Tautology    : 134
% 4.90/1.90  #SimpNegUnit  : 29
% 4.90/1.90  #BackRed      : 17
% 4.90/1.90  
% 4.90/1.90  #Partial instantiations: 0
% 4.90/1.90  #Strategies tried      : 1
% 4.90/1.90  
% 4.90/1.90  Timing (in seconds)
% 4.90/1.90  ----------------------
% 4.90/1.90  Preprocessing        : 0.43
% 4.90/1.90  Parsing              : 0.21
% 4.90/1.90  CNF conversion       : 0.05
% 4.90/1.90  Main loop            : 0.68
% 4.90/1.90  Inferencing          : 0.23
% 4.90/1.90  Reduction            : 0.24
% 4.90/1.90  Demodulation         : 0.17
% 4.90/1.90  BG Simplification    : 0.03
% 4.90/1.90  Subsumption          : 0.13
% 4.90/1.90  Abstraction          : 0.02
% 4.90/1.90  MUC search           : 0.00
% 4.90/1.90  Cooper               : 0.00
% 4.90/1.90  Total                : 1.16
% 4.90/1.90  Index Insertion      : 0.00
% 4.90/1.90  Index Deletion       : 0.00
% 4.90/1.90  Index Matching       : 0.00
% 4.90/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
