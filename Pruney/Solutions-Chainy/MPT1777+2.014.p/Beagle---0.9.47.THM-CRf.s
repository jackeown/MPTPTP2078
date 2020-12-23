%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:34 EST 2020

% Result     : Theorem 4.97s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :  123 (1704 expanded)
%              Number of leaves         :   44 ( 601 expanded)
%              Depth                    :   19
%              Number of atoms          :  262 (7602 expanded)
%              Number of equality atoms :   37 (1005 expanded)
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

tff(f_229,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_180,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_107,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_117,plain,(
    ! [B_292,A_293] :
      ( l1_pre_topc(B_292)
      | ~ m1_pre_topc(B_292,A_293)
      | ~ l1_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_130,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_123])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    ! [A_290] :
      ( u1_struct_0(A_290) = k2_struct_0(A_290)
      | ~ l1_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_97])).

tff(c_98,plain,(
    ! [A_291] :
      ( u1_struct_0(A_291) = k2_struct_0(A_291)
      | ~ l1_pre_topc(A_291) ) ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_105,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_98])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_108,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58])).

tff(c_142,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_108])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

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
    ! [A_33] :
      ( m1_pre_topc(A_33,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_141,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_148,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_54])).

tff(c_159,plain,(
    ! [A_295] :
      ( m1_subset_1(u1_pre_topc(A_295),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_295))))
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_162,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_159])).

tff(c_173,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_162])).

tff(c_215,plain,(
    ! [A_298,B_299] :
      ( v1_pre_topc(g1_pre_topc(A_298,B_299))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(k1_zfmisc_1(A_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_227,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_173,c_215])).

tff(c_235,plain,(
    v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_227])).

tff(c_300,plain,(
    ! [A_304] :
      ( g1_pre_topc(u1_struct_0(A_304),u1_pre_topc(A_304)) = A_304
      | ~ v1_pre_topc(A_304)
      | ~ l1_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_318,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_300])).

tff(c_330,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_235,c_318])).

tff(c_467,plain,(
    ! [D_315,B_316,C_317,A_318] :
      ( D_315 = B_316
      | g1_pre_topc(C_317,D_315) != g1_pre_topc(A_318,B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(k1_zfmisc_1(A_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_479,plain,(
    ! [D_315,C_317] :
      ( u1_pre_topc('#skF_3') = D_315
      | g1_pre_topc(C_317,D_315) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_467])).

tff(c_505,plain,(
    ! [D_319,C_320] :
      ( u1_pre_topc('#skF_3') = D_319
      | g1_pre_topc(C_320,D_319) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_479])).

tff(c_515,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_505])).

tff(c_534,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_148])).

tff(c_165,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_159])).

tff(c_175,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_165])).

tff(c_587,plain,(
    ! [C_324,A_325,D_326,B_327] :
      ( C_324 = A_325
      | g1_pre_topc(C_324,D_326) != g1_pre_topc(A_325,B_327)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(k1_zfmisc_1(A_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_595,plain,(
    ! [C_324,D_326] :
      ( k2_struct_0('#skF_4') = C_324
      | g1_pre_topc(C_324,D_326) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_587])).

tff(c_612,plain,(
    ! [C_328,D_329] :
      ( k2_struct_0('#skF_4') = C_328
      | g1_pre_topc(C_328,D_329) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_595])).

tff(c_622,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_612])).

tff(c_631,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_141])).

tff(c_689,plain,(
    ! [A_330,B_331] :
      ( m1_pre_topc(A_330,g1_pre_topc(u1_struct_0(B_331),u1_pre_topc(B_331)))
      | ~ m1_pre_topc(A_330,B_331)
      | ~ l1_pre_topc(B_331)
      | ~ l1_pre_topc(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_707,plain,(
    ! [A_330] :
      ( m1_pre_topc(A_330,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_4')))
      | ~ m1_pre_topc(A_330,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_689])).

tff(c_736,plain,(
    ! [A_332] :
      ( m1_pre_topc(A_332,'#skF_4')
      | ~ m1_pre_topc(A_332,'#skF_3')
      | ~ l1_pre_topc(A_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_330,c_631,c_707])).

tff(c_744,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_736])).

tff(c_750,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_744])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_143,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_52])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1485,plain,(
    ! [D_368,E_371,B_370,A_367,C_369,G_372] :
      ( r1_tmap_1(D_368,B_370,E_371,G_372)
      | ~ r1_tmap_1(C_369,B_370,k3_tmap_1(A_367,B_370,D_368,C_369,E_371),G_372)
      | ~ m1_subset_1(G_372,u1_struct_0(C_369))
      | ~ m1_subset_1(G_372,u1_struct_0(D_368))
      | ~ m1_pre_topc(C_369,D_368)
      | ~ v1_tsep_1(C_369,D_368)
      | ~ m1_subset_1(E_371,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_368),u1_struct_0(B_370))))
      | ~ v1_funct_2(E_371,u1_struct_0(D_368),u1_struct_0(B_370))
      | ~ v1_funct_1(E_371)
      | ~ m1_pre_topc(D_368,A_367)
      | v2_struct_0(D_368)
      | ~ m1_pre_topc(C_369,A_367)
      | v2_struct_0(C_369)
      | ~ l1_pre_topc(B_370)
      | ~ v2_pre_topc(B_370)
      | v2_struct_0(B_370)
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1487,plain,
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
    inference(resolution,[status(thm)],[c_82,c_1485])).

tff(c_1490,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_142,c_105,c_137,c_180,c_105,c_137,c_750,c_143,c_137,c_143,c_631,c_1487])).

tff(c_1491,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_1490])).

tff(c_283,plain,(
    ! [B_302,A_303] :
      ( v2_pre_topc(B_302)
      | ~ m1_pre_topc(B_302,A_303)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_289,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_283])).

tff(c_296,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_289])).

tff(c_26,plain,(
    ! [A_22] :
      ( v3_pre_topc(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(u1_struct_0(B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_970,plain,(
    ! [B_340,A_341] :
      ( v1_tsep_1(B_340,A_341)
      | ~ v3_pre_topc(u1_struct_0(B_340),A_341)
      | ~ m1_subset_1(u1_struct_0(B_340),k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ m1_pre_topc(B_340,A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1736,plain,(
    ! [B_378,A_379] :
      ( v1_tsep_1(B_378,A_379)
      | ~ v3_pre_topc(u1_struct_0(B_378),A_379)
      | ~ v2_pre_topc(A_379)
      | ~ m1_pre_topc(B_378,A_379)
      | ~ l1_pre_topc(A_379) ) ),
    inference(resolution,[status(thm)],[c_34,c_970])).

tff(c_2515,plain,(
    ! [A_429] :
      ( v1_tsep_1('#skF_3',A_429)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_429)
      | ~ v2_pre_topc(A_429)
      | ~ m1_pre_topc('#skF_3',A_429)
      | ~ l1_pre_topc(A_429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_1736])).

tff(c_2528,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_2515])).

tff(c_2536,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_130,c_750,c_2528])).

tff(c_2538,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1491,c_2536])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.90  
% 4.97/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.97/1.91  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.97/1.91  
% 4.97/1.91  %Foreground sorts:
% 4.97/1.91  
% 4.97/1.91  
% 4.97/1.91  %Background operators:
% 4.97/1.91  
% 4.97/1.91  
% 4.97/1.91  %Foreground operators:
% 4.97/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.97/1.91  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.97/1.91  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.97/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.97/1.91  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.97/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.97/1.91  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.97/1.91  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.97/1.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.97/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.97/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.97/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.97/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.97/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.97/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.97/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.97/1.91  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.97/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.97/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.97/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.97/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.97/1.91  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.97/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.97/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.97/1.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.97/1.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.97/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.97/1.91  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.97/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.97/1.91  
% 5.35/1.93  tff(f_229, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.35/1.93  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.35/1.93  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.35/1.93  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.35/1.93  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.35/1.93  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 5.35/1.93  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 5.35/1.93  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.35/1.93  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 5.35/1.93  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.35/1.93  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 5.35/1.93  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.35/1.93  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.35/1.93  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.35/1.93  tff(f_107, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.35/1.93  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_117, plain, (![B_292, A_293]: (l1_pre_topc(B_292) | ~m1_pre_topc(B_292, A_293) | ~l1_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.35/1.93  tff(c_123, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_117])).
% 5.35/1.93  tff(c_130, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_123])).
% 5.35/1.93  tff(c_12, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.35/1.93  tff(c_93, plain, (![A_290]: (u1_struct_0(A_290)=k2_struct_0(A_290) | ~l1_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.35/1.93  tff(c_97, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_12, c_93])).
% 5.35/1.93  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_97])).
% 5.35/1.93  tff(c_98, plain, (![A_291]: (u1_struct_0(A_291)=k2_struct_0(A_291) | ~l1_pre_topc(A_291))), inference(resolution, [status(thm)], [c_12, c_93])).
% 5.35/1.93  tff(c_105, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_98])).
% 5.35/1.93  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_108, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58])).
% 5.35/1.93  tff(c_142, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_108])).
% 5.35/1.93  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_56])).
% 5.35/1.93  tff(c_180, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 5.35/1.93  tff(c_126, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_117])).
% 5.35/1.93  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126])).
% 5.35/1.93  tff(c_36, plain, (![A_33]: (m1_pre_topc(A_33, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.35/1.93  tff(c_141, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_97])).
% 5.35/1.93  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_148, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_54])).
% 5.35/1.93  tff(c_159, plain, (![A_295]: (m1_subset_1(u1_pre_topc(A_295), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_295)))) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.35/1.93  tff(c_162, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_159])).
% 5.35/1.93  tff(c_173, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_162])).
% 5.35/1.93  tff(c_215, plain, (![A_298, B_299]: (v1_pre_topc(g1_pre_topc(A_298, B_299)) | ~m1_subset_1(B_299, k1_zfmisc_1(k1_zfmisc_1(A_298))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.35/1.93  tff(c_227, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_173, c_215])).
% 5.35/1.93  tff(c_235, plain, (v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_227])).
% 5.35/1.93  tff(c_300, plain, (![A_304]: (g1_pre_topc(u1_struct_0(A_304), u1_pre_topc(A_304))=A_304 | ~v1_pre_topc(A_304) | ~l1_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.35/1.93  tff(c_318, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_300])).
% 5.35/1.93  tff(c_330, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_235, c_318])).
% 5.35/1.93  tff(c_467, plain, (![D_315, B_316, C_317, A_318]: (D_315=B_316 | g1_pre_topc(C_317, D_315)!=g1_pre_topc(A_318, B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(k1_zfmisc_1(A_318))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.35/1.93  tff(c_479, plain, (![D_315, C_317]: (u1_pre_topc('#skF_3')=D_315 | g1_pre_topc(C_317, D_315)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_148, c_467])).
% 5.35/1.93  tff(c_505, plain, (![D_319, C_320]: (u1_pre_topc('#skF_3')=D_319 | g1_pre_topc(C_320, D_319)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_479])).
% 5.35/1.93  tff(c_515, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_330, c_505])).
% 5.35/1.93  tff(c_534, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_515, c_148])).
% 5.35/1.93  tff(c_165, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_159])).
% 5.35/1.93  tff(c_175, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_165])).
% 5.35/1.93  tff(c_587, plain, (![C_324, A_325, D_326, B_327]: (C_324=A_325 | g1_pre_topc(C_324, D_326)!=g1_pre_topc(A_325, B_327) | ~m1_subset_1(B_327, k1_zfmisc_1(k1_zfmisc_1(A_325))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.35/1.93  tff(c_595, plain, (![C_324, D_326]: (k2_struct_0('#skF_4')=C_324 | g1_pre_topc(C_324, D_326)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_330, c_587])).
% 5.35/1.93  tff(c_612, plain, (![C_328, D_329]: (k2_struct_0('#skF_4')=C_328 | g1_pre_topc(C_328, D_329)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_595])).
% 5.35/1.93  tff(c_622, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_534, c_612])).
% 5.35/1.93  tff(c_631, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_622, c_141])).
% 5.35/1.93  tff(c_689, plain, (![A_330, B_331]: (m1_pre_topc(A_330, g1_pre_topc(u1_struct_0(B_331), u1_pre_topc(B_331))) | ~m1_pre_topc(A_330, B_331) | ~l1_pre_topc(B_331) | ~l1_pre_topc(A_330))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.35/1.93  tff(c_707, plain, (![A_330]: (m1_pre_topc(A_330, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_4'))) | ~m1_pre_topc(A_330, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_330))), inference(superposition, [status(thm), theory('equality')], [c_515, c_689])).
% 5.35/1.93  tff(c_736, plain, (![A_332]: (m1_pre_topc(A_332, '#skF_4') | ~m1_pre_topc(A_332, '#skF_3') | ~l1_pre_topc(A_332))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_330, c_631, c_707])).
% 5.35/1.93  tff(c_744, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_736])).
% 5.35/1.93  tff(c_750, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_744])).
% 5.35/1.93  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_143, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_52])).
% 5.35/1.93  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.35/1.93  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 5.35/1.93  tff(c_1485, plain, (![D_368, E_371, B_370, A_367, C_369, G_372]: (r1_tmap_1(D_368, B_370, E_371, G_372) | ~r1_tmap_1(C_369, B_370, k3_tmap_1(A_367, B_370, D_368, C_369, E_371), G_372) | ~m1_subset_1(G_372, u1_struct_0(C_369)) | ~m1_subset_1(G_372, u1_struct_0(D_368)) | ~m1_pre_topc(C_369, D_368) | ~v1_tsep_1(C_369, D_368) | ~m1_subset_1(E_371, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_368), u1_struct_0(B_370)))) | ~v1_funct_2(E_371, u1_struct_0(D_368), u1_struct_0(B_370)) | ~v1_funct_1(E_371) | ~m1_pre_topc(D_368, A_367) | v2_struct_0(D_368) | ~m1_pre_topc(C_369, A_367) | v2_struct_0(C_369) | ~l1_pre_topc(B_370) | ~v2_pre_topc(B_370) | v2_struct_0(B_370) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.35/1.93  tff(c_1487, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_1485])).
% 5.35/1.93  tff(c_1490, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_142, c_105, c_137, c_180, c_105, c_137, c_750, c_143, c_137, c_143, c_631, c_1487])).
% 5.35/1.93  tff(c_1491, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_1490])).
% 5.35/1.93  tff(c_283, plain, (![B_302, A_303]: (v2_pre_topc(B_302) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.35/1.93  tff(c_289, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_283])).
% 5.35/1.93  tff(c_296, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_289])).
% 5.35/1.93  tff(c_26, plain, (![A_22]: (v3_pre_topc(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.35/1.93  tff(c_34, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.35/1.93  tff(c_970, plain, (![B_340, A_341]: (v1_tsep_1(B_340, A_341) | ~v3_pre_topc(u1_struct_0(B_340), A_341) | ~m1_subset_1(u1_struct_0(B_340), k1_zfmisc_1(u1_struct_0(A_341))) | ~m1_pre_topc(B_340, A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.35/1.93  tff(c_1736, plain, (![B_378, A_379]: (v1_tsep_1(B_378, A_379) | ~v3_pre_topc(u1_struct_0(B_378), A_379) | ~v2_pre_topc(A_379) | ~m1_pre_topc(B_378, A_379) | ~l1_pre_topc(A_379))), inference(resolution, [status(thm)], [c_34, c_970])).
% 5.35/1.93  tff(c_2515, plain, (![A_429]: (v1_tsep_1('#skF_3', A_429) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_429) | ~v2_pre_topc(A_429) | ~m1_pre_topc('#skF_3', A_429) | ~l1_pre_topc(A_429))), inference(superposition, [status(thm), theory('equality')], [c_631, c_1736])).
% 5.35/1.93  tff(c_2528, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_2515])).
% 5.35/1.93  tff(c_2536, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_130, c_750, c_2528])).
% 5.35/1.93  tff(c_2538, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1491, c_2536])).
% 5.35/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/1.93  
% 5.35/1.93  Inference rules
% 5.35/1.93  ----------------------
% 5.35/1.93  #Ref     : 6
% 5.35/1.93  #Sup     : 505
% 5.35/1.93  #Fact    : 0
% 5.35/1.93  #Define  : 0
% 5.35/1.93  #Split   : 15
% 5.35/1.93  #Chain   : 0
% 5.35/1.93  #Close   : 0
% 5.35/1.93  
% 5.35/1.93  Ordering : KBO
% 5.35/1.93  
% 5.35/1.93  Simplification rules
% 5.35/1.93  ----------------------
% 5.35/1.93  #Subsume      : 64
% 5.35/1.93  #Demod        : 731
% 5.35/1.93  #Tautology    : 181
% 5.35/1.93  #SimpNegUnit  : 22
% 5.35/1.93  #BackRed      : 17
% 5.35/1.93  
% 5.35/1.93  #Partial instantiations: 0
% 5.35/1.93  #Strategies tried      : 1
% 5.35/1.93  
% 5.35/1.93  Timing (in seconds)
% 5.35/1.93  ----------------------
% 5.35/1.93  Preprocessing        : 0.39
% 5.35/1.93  Parsing              : 0.20
% 5.35/1.93  CNF conversion       : 0.05
% 5.35/1.93  Main loop            : 0.74
% 5.35/1.93  Inferencing          : 0.24
% 5.35/1.93  Reduction            : 0.28
% 5.35/1.93  Demodulation         : 0.20
% 5.35/1.93  BG Simplification    : 0.03
% 5.35/1.93  Subsumption          : 0.15
% 5.35/1.93  Abstraction          : 0.03
% 5.35/1.93  MUC search           : 0.00
% 5.35/1.93  Cooper               : 0.00
% 5.35/1.93  Total                : 1.18
% 5.35/1.93  Index Insertion      : 0.00
% 5.35/1.93  Index Deletion       : 0.00
% 5.35/1.93  Index Matching       : 0.00
% 5.35/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
