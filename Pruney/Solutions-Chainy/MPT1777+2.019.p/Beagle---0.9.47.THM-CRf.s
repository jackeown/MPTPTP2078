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

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.47s
% Verified   : 
% Statistics : Number of formulae       :  126 (1067 expanded)
%              Number of leaves         :   44 ( 382 expanded)
%              Depth                    :   16
%              Number of atoms          :  269 (4827 expanded)
%              Number of equality atoms :   38 ( 665 expanded)
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

tff(f_232,negated_conjecture,(
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

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_183,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_110,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_117,plain,(
    ! [B_293,A_294] :
      ( l1_pre_topc(B_293)
      | ~ m1_pre_topc(B_293,A_294)
      | ~ l1_pre_topc(A_294) ) ),
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
    ! [A_291] :
      ( u1_struct_0(A_291) = k2_struct_0(A_291)
      | ~ l1_struct_0(A_291) ) ),
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
    ! [A_292] :
      ( u1_struct_0(A_292) = k2_struct_0(A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_105,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_98])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_108,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58])).

tff(c_142,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_108])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

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
    ! [A_34] :
      ( m1_pre_topc(A_34,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_198,plain,(
    ! [A_299] :
      ( g1_pre_topc(u1_struct_0(A_299),u1_pre_topc(A_299)) = A_299
      | ~ v1_pre_topc(A_299)
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_210,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_198])).

tff(c_222,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_210])).

tff(c_230,plain,(
    ~ v1_pre_topc('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_222])).

tff(c_141,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_148,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_54])).

tff(c_264,plain,(
    ! [B_302,A_303] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_302),u1_pre_topc(B_302)))
      | ~ m1_pre_topc(B_302,A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_270,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_264])).

tff(c_277,plain,(
    v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_148,c_141,c_270])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_277])).

tff(c_280,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_222])).

tff(c_159,plain,(
    ! [A_296] :
      ( m1_subset_1(u1_pre_topc(A_296),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_296))))
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_159])).

tff(c_173,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_162])).

tff(c_495,plain,(
    ! [C_314,A_315,D_316,B_317] :
      ( C_314 = A_315
      | g1_pre_topc(C_314,D_316) != g1_pre_topc(A_315,B_317)
      | ~ m1_subset_1(B_317,k1_zfmisc_1(k1_zfmisc_1(A_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_507,plain,(
    ! [C_314,D_316] :
      ( k2_struct_0('#skF_3') = C_314
      | g1_pre_topc(C_314,D_316) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_495])).

tff(c_512,plain,(
    ! [C_318,D_319] :
      ( k2_struct_0('#skF_3') = C_318
      | g1_pre_topc(C_318,D_319) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_507])).

tff(c_522,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_512])).

tff(c_528,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_148])).

tff(c_165,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_159])).

tff(c_175,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_165])).

tff(c_710,plain,(
    ! [D_328,B_329,C_330,A_331] :
      ( D_328 = B_329
      | g1_pre_topc(C_330,D_328) != g1_pre_topc(A_331,B_329)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(k1_zfmisc_1(A_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_718,plain,(
    ! [D_328,C_330] :
      ( u1_pre_topc('#skF_4') = D_328
      | g1_pre_topc(C_330,D_328) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_710])).

tff(c_727,plain,(
    ! [D_332,C_333] :
      ( u1_pre_topc('#skF_4') = D_332
      | g1_pre_topc(C_333,D_332) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_718])).

tff(c_737,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_727])).

tff(c_530,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_141])).

tff(c_785,plain,(
    ! [A_335,B_336] :
      ( m1_pre_topc(A_335,g1_pre_topc(u1_struct_0(B_336),u1_pre_topc(B_336)))
      | ~ m1_pre_topc(A_335,B_336)
      | ~ l1_pre_topc(B_336)
      | ~ l1_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_809,plain,(
    ! [A_335] :
      ( m1_pre_topc(A_335,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_335,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_785])).

tff(c_842,plain,(
    ! [A_337] :
      ( m1_pre_topc(A_337,'#skF_4')
      | ~ m1_pre_topc(A_337,'#skF_3')
      | ~ l1_pre_topc(A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_280,c_737,c_809])).

tff(c_857,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_842])).

tff(c_869,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_857])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_143,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_52])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1692,plain,(
    ! [B_374,C_371,A_372,G_376,D_375,E_373] :
      ( r1_tmap_1(D_375,B_374,E_373,G_376)
      | ~ r1_tmap_1(C_371,B_374,k3_tmap_1(A_372,B_374,D_375,C_371,E_373),G_376)
      | ~ m1_subset_1(G_376,u1_struct_0(C_371))
      | ~ m1_subset_1(G_376,u1_struct_0(D_375))
      | ~ m1_pre_topc(C_371,D_375)
      | ~ v1_tsep_1(C_371,D_375)
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_375),u1_struct_0(B_374))))
      | ~ v1_funct_2(E_373,u1_struct_0(D_375),u1_struct_0(B_374))
      | ~ v1_funct_1(E_373)
      | ~ m1_pre_topc(D_375,A_372)
      | v2_struct_0(D_375)
      | ~ m1_pre_topc(C_371,A_372)
      | v2_struct_0(C_371)
      | ~ l1_pre_topc(B_374)
      | ~ v2_pre_topc(B_374)
      | v2_struct_0(B_374)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1694,plain,
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
    inference(resolution,[status(thm)],[c_82,c_1692])).

tff(c_1697,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_142,c_105,c_137,c_180,c_105,c_137,c_869,c_143,c_137,c_143,c_530,c_1694])).

tff(c_1698,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_1697])).

tff(c_181,plain,(
    ! [B_297,A_298] :
      ( v2_pre_topc(B_297)
      | ~ m1_pre_topc(B_297,A_298)
      | ~ l1_pre_topc(A_298)
      | ~ v2_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_187,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_181])).

tff(c_194,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_187])).

tff(c_22,plain,(
    ! [A_20] :
      ( v3_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [B_33,A_31] :
      ( m1_subset_1(u1_struct_0(B_33),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(B_33,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1057,plain,(
    ! [B_342,A_343] :
      ( v1_tsep_1(B_342,A_343)
      | ~ v3_pre_topc(u1_struct_0(B_342),A_343)
      | ~ m1_subset_1(u1_struct_0(B_342),k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_pre_topc(B_342,A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2153,plain,(
    ! [B_395,A_396] :
      ( v1_tsep_1(B_395,A_396)
      | ~ v3_pre_topc(u1_struct_0(B_395),A_396)
      | ~ v2_pre_topc(A_396)
      | ~ m1_pre_topc(B_395,A_396)
      | ~ l1_pre_topc(A_396) ) ),
    inference(resolution,[status(thm)],[c_34,c_1057])).

tff(c_2910,plain,(
    ! [A_430] :
      ( v1_tsep_1('#skF_3',A_430)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_430)
      | ~ v2_pre_topc(A_430)
      | ~ m1_pre_topc('#skF_3',A_430)
      | ~ l1_pre_topc(A_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_2153])).

tff(c_2923,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_2910])).

tff(c_2931,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_130,c_869,c_2923])).

tff(c_2933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1698,c_2931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/1.96  
% 5.29/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.29/1.96  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.29/1.96  
% 5.29/1.96  %Foreground sorts:
% 5.29/1.96  
% 5.29/1.96  
% 5.29/1.96  %Background operators:
% 5.29/1.96  
% 5.29/1.96  
% 5.29/1.96  %Foreground operators:
% 5.29/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.29/1.96  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.29/1.96  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.29/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.29/1.96  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.29/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/1.96  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.29/1.96  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.29/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.29/1.96  tff('#skF_7', type, '#skF_7': $i).
% 5.29/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.29/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.29/1.96  tff('#skF_6', type, '#skF_6': $i).
% 5.29/1.96  tff('#skF_2', type, '#skF_2': $i).
% 5.29/1.96  tff('#skF_3', type, '#skF_3': $i).
% 5.29/1.96  tff('#skF_1', type, '#skF_1': $i).
% 5.29/1.96  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.29/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/1.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.29/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.29/1.96  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.29/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.29/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/1.96  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.29/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.29/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.29/1.96  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.29/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/1.96  
% 5.47/1.98  tff(f_232, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.47/1.98  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.47/1.98  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.47/1.98  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.47/1.98  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.47/1.98  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.47/1.98  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 5.47/1.98  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.47/1.98  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 5.47/1.98  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.47/1.98  tff(f_183, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 5.47/1.98  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.47/1.98  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.47/1.98  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.47/1.98  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.47/1.98  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_117, plain, (![B_293, A_294]: (l1_pre_topc(B_293) | ~m1_pre_topc(B_293, A_294) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.47/1.98  tff(c_123, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_117])).
% 5.47/1.98  tff(c_130, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_123])).
% 5.47/1.98  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.47/1.98  tff(c_93, plain, (![A_291]: (u1_struct_0(A_291)=k2_struct_0(A_291) | ~l1_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.47/1.98  tff(c_97, plain, (![A_6]: (u1_struct_0(A_6)=k2_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_93])).
% 5.47/1.98  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_97])).
% 5.47/1.98  tff(c_98, plain, (![A_292]: (u1_struct_0(A_292)=k2_struct_0(A_292) | ~l1_pre_topc(A_292))), inference(resolution, [status(thm)], [c_8, c_93])).
% 5.47/1.98  tff(c_105, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_98])).
% 5.47/1.98  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_108, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58])).
% 5.47/1.98  tff(c_142, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_108])).
% 5.47/1.98  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_56])).
% 5.47/1.98  tff(c_180, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 5.47/1.98  tff(c_126, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_117])).
% 5.47/1.98  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126])).
% 5.47/1.98  tff(c_36, plain, (![A_34]: (m1_pre_topc(A_34, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.47/1.98  tff(c_198, plain, (![A_299]: (g1_pre_topc(u1_struct_0(A_299), u1_pre_topc(A_299))=A_299 | ~v1_pre_topc(A_299) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.47/1.98  tff(c_210, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_198])).
% 5.47/1.98  tff(c_222, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_210])).
% 5.47/1.98  tff(c_230, plain, (~v1_pre_topc('#skF_4')), inference(splitLeft, [status(thm)], [c_222])).
% 5.47/1.98  tff(c_141, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_97])).
% 5.47/1.98  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_148, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_54])).
% 5.47/1.98  tff(c_264, plain, (![B_302, A_303]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_302), u1_pre_topc(B_302))) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.47/1.98  tff(c_270, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_264])).
% 5.47/1.98  tff(c_277, plain, (v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_148, c_141, c_270])).
% 5.47/1.98  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_277])).
% 5.47/1.98  tff(c_280, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_222])).
% 5.47/1.98  tff(c_159, plain, (![A_296]: (m1_subset_1(u1_pre_topc(A_296), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_296)))) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.47/1.98  tff(c_162, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_159])).
% 5.47/1.98  tff(c_173, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_162])).
% 5.47/1.98  tff(c_495, plain, (![C_314, A_315, D_316, B_317]: (C_314=A_315 | g1_pre_topc(C_314, D_316)!=g1_pre_topc(A_315, B_317) | ~m1_subset_1(B_317, k1_zfmisc_1(k1_zfmisc_1(A_315))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.47/1.98  tff(c_507, plain, (![C_314, D_316]: (k2_struct_0('#skF_3')=C_314 | g1_pre_topc(C_314, D_316)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_148, c_495])).
% 5.47/1.98  tff(c_512, plain, (![C_318, D_319]: (k2_struct_0('#skF_3')=C_318 | g1_pre_topc(C_318, D_319)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_507])).
% 5.47/1.98  tff(c_522, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_280, c_512])).
% 5.47/1.98  tff(c_528, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_522, c_148])).
% 5.47/1.98  tff(c_165, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_159])).
% 5.47/1.98  tff(c_175, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_165])).
% 5.47/1.98  tff(c_710, plain, (![D_328, B_329, C_330, A_331]: (D_328=B_329 | g1_pre_topc(C_330, D_328)!=g1_pre_topc(A_331, B_329) | ~m1_subset_1(B_329, k1_zfmisc_1(k1_zfmisc_1(A_331))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.47/1.98  tff(c_718, plain, (![D_328, C_330]: (u1_pre_topc('#skF_4')=D_328 | g1_pre_topc(C_330, D_328)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_280, c_710])).
% 5.47/1.98  tff(c_727, plain, (![D_332, C_333]: (u1_pre_topc('#skF_4')=D_332 | g1_pre_topc(C_333, D_332)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_718])).
% 5.47/1.98  tff(c_737, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_528, c_727])).
% 5.47/1.98  tff(c_530, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_522, c_141])).
% 5.47/1.98  tff(c_785, plain, (![A_335, B_336]: (m1_pre_topc(A_335, g1_pre_topc(u1_struct_0(B_336), u1_pre_topc(B_336))) | ~m1_pre_topc(A_335, B_336) | ~l1_pre_topc(B_336) | ~l1_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.47/1.98  tff(c_809, plain, (![A_335]: (m1_pre_topc(A_335, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_335, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_335))), inference(superposition, [status(thm), theory('equality')], [c_530, c_785])).
% 5.47/1.98  tff(c_842, plain, (![A_337]: (m1_pre_topc(A_337, '#skF_4') | ~m1_pre_topc(A_337, '#skF_3') | ~l1_pre_topc(A_337))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_280, c_737, c_809])).
% 5.47/1.98  tff(c_857, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_842])).
% 5.47/1.98  tff(c_869, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_857])).
% 5.47/1.98  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_143, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_52])).
% 5.47/1.98  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_232])).
% 5.47/1.98  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 5.47/1.98  tff(c_1692, plain, (![B_374, C_371, A_372, G_376, D_375, E_373]: (r1_tmap_1(D_375, B_374, E_373, G_376) | ~r1_tmap_1(C_371, B_374, k3_tmap_1(A_372, B_374, D_375, C_371, E_373), G_376) | ~m1_subset_1(G_376, u1_struct_0(C_371)) | ~m1_subset_1(G_376, u1_struct_0(D_375)) | ~m1_pre_topc(C_371, D_375) | ~v1_tsep_1(C_371, D_375) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_375), u1_struct_0(B_374)))) | ~v1_funct_2(E_373, u1_struct_0(D_375), u1_struct_0(B_374)) | ~v1_funct_1(E_373) | ~m1_pre_topc(D_375, A_372) | v2_struct_0(D_375) | ~m1_pre_topc(C_371, A_372) | v2_struct_0(C_371) | ~l1_pre_topc(B_374) | ~v2_pre_topc(B_374) | v2_struct_0(B_374) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(cnfTransformation, [status(thm)], [f_183])).
% 5.47/1.98  tff(c_1694, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_1692])).
% 5.47/1.98  tff(c_1697, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_142, c_105, c_137, c_180, c_105, c_137, c_869, c_143, c_137, c_143, c_530, c_1694])).
% 5.47/1.98  tff(c_1698, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_1697])).
% 5.47/1.98  tff(c_181, plain, (![B_297, A_298]: (v2_pre_topc(B_297) | ~m1_pre_topc(B_297, A_298) | ~l1_pre_topc(A_298) | ~v2_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.47/1.98  tff(c_187, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_181])).
% 5.47/1.98  tff(c_194, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_187])).
% 5.47/1.98  tff(c_22, plain, (![A_20]: (v3_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.47/1.98  tff(c_34, plain, (![B_33, A_31]: (m1_subset_1(u1_struct_0(B_33), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(B_33, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.47/1.98  tff(c_1057, plain, (![B_342, A_343]: (v1_tsep_1(B_342, A_343) | ~v3_pre_topc(u1_struct_0(B_342), A_343) | ~m1_subset_1(u1_struct_0(B_342), k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_pre_topc(B_342, A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.47/1.98  tff(c_2153, plain, (![B_395, A_396]: (v1_tsep_1(B_395, A_396) | ~v3_pre_topc(u1_struct_0(B_395), A_396) | ~v2_pre_topc(A_396) | ~m1_pre_topc(B_395, A_396) | ~l1_pre_topc(A_396))), inference(resolution, [status(thm)], [c_34, c_1057])).
% 5.47/1.98  tff(c_2910, plain, (![A_430]: (v1_tsep_1('#skF_3', A_430) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_430) | ~v2_pre_topc(A_430) | ~m1_pre_topc('#skF_3', A_430) | ~l1_pre_topc(A_430))), inference(superposition, [status(thm), theory('equality')], [c_530, c_2153])).
% 5.47/1.98  tff(c_2923, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_2910])).
% 5.47/1.98  tff(c_2931, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_130, c_869, c_2923])).
% 5.47/1.98  tff(c_2933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1698, c_2931])).
% 5.47/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.47/1.98  
% 5.47/1.98  Inference rules
% 5.47/1.98  ----------------------
% 5.47/1.98  #Ref     : 3
% 5.47/1.98  #Sup     : 595
% 5.47/1.98  #Fact    : 0
% 5.47/1.98  #Define  : 0
% 5.47/1.98  #Split   : 15
% 5.47/1.98  #Chain   : 0
% 5.47/1.98  #Close   : 0
% 5.47/1.98  
% 5.47/1.98  Ordering : KBO
% 5.47/1.98  
% 5.47/1.98  Simplification rules
% 5.47/1.98  ----------------------
% 5.47/1.98  #Subsume      : 88
% 5.47/1.98  #Demod        : 926
% 5.47/1.98  #Tautology    : 212
% 5.47/1.98  #SimpNegUnit  : 21
% 5.47/1.98  #BackRed      : 14
% 5.47/1.98  
% 5.47/1.98  #Partial instantiations: 0
% 5.47/1.98  #Strategies tried      : 1
% 5.47/1.98  
% 5.47/1.98  Timing (in seconds)
% 5.47/1.98  ----------------------
% 5.47/1.99  Preprocessing        : 0.40
% 5.47/1.99  Parsing              : 0.20
% 5.47/1.99  CNF conversion       : 0.05
% 5.47/1.99  Main loop            : 0.79
% 5.47/1.99  Inferencing          : 0.24
% 5.47/1.99  Reduction            : 0.30
% 5.47/1.99  Demodulation         : 0.22
% 5.47/1.99  BG Simplification    : 0.03
% 5.47/1.99  Subsumption          : 0.17
% 5.47/1.99  Abstraction          : 0.03
% 5.47/1.99  MUC search           : 0.00
% 5.47/1.99  Cooper               : 0.00
% 5.47/1.99  Total                : 1.24
% 5.47/1.99  Index Insertion      : 0.00
% 5.47/1.99  Index Deletion       : 0.00
% 5.47/1.99  Index Matching       : 0.00
% 5.47/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
