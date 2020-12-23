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
% DateTime   : Thu Dec  3 10:27:33 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  149 (2490 expanded)
%              Number of leaves         :   48 ( 885 expanded)
%              Depth                    :   17
%              Number of atoms          :  327 (14047 expanded)
%              Number of equality atoms :   30 (1809 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3

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

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_251,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_102,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_129,axiom,(
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

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_202,axiom,(
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

tff(c_114,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_108,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_102,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_78,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_112,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_110,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_106,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_100,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_96,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_126,plain,(
    ! [B_302,A_303] :
      ( l1_pre_topc(B_302)
      | ~ m1_pre_topc(B_302,A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_132,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_126])).

tff(c_139,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_132])).

tff(c_143,plain,(
    ! [B_304,A_305] :
      ( v2_pre_topc(B_304)
      | ~ m1_pre_topc(B_304,A_305)
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_152,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_143])).

tff(c_159,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_152])).

tff(c_135,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_126])).

tff(c_142,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_135])).

tff(c_88,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_162,plain,(
    ! [A_308] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_308),u1_pre_topc(A_308)))
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_165,plain,
    ( v1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_162])).

tff(c_167,plain,(
    v1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_142,c_165])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_25] :
      ( m1_subset_1(u1_pre_topc(A_25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25))))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_205,plain,(
    ! [C_313,A_314,D_315,B_316] :
      ( C_313 = A_314
      | g1_pre_topc(C_313,D_315) != g1_pre_topc(A_314,B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(k1_zfmisc_1(A_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_213,plain,(
    ! [C_313,D_315] :
      ( u1_struct_0('#skF_6') = C_313
      | g1_pre_topc(C_313,D_315) != '#skF_7'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_205])).

tff(c_230,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_233,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_230])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_233])).

tff(c_240,plain,(
    ! [C_320,D_321] :
      ( u1_struct_0('#skF_6') = C_320
      | g1_pre_topc(C_320,D_321) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_250,plain,(
    ! [A_322] :
      ( u1_struct_0(A_322) = u1_struct_0('#skF_6')
      | A_322 != '#skF_7'
      | ~ v1_pre_topc(A_322)
      | ~ l1_pre_topc(A_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_240])).

tff(c_253,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_167,c_250])).

tff(c_259,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_253])).

tff(c_92,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_262,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_92])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_261,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_90])).

tff(c_70,plain,(
    ! [A_46] :
      ( m1_pre_topc(A_46,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_274,plain,
    ( g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7')) = '#skF_7'
    | ~ v1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_2])).

tff(c_292,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_167,c_274])).

tff(c_239,plain,(
    m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_306,plain,(
    ! [D_323,B_324,C_325,A_326] :
      ( D_323 = B_324
      | g1_pre_topc(C_325,D_323) != g1_pre_topc(A_326,B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(k1_zfmisc_1(A_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_314,plain,(
    ! [D_323,C_325] :
      ( u1_pre_topc('#skF_6') = D_323
      | g1_pre_topc(C_325,D_323) != '#skF_7'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_306])).

tff(c_342,plain,(
    ! [D_327,C_328] :
      ( u1_pre_topc('#skF_6') = D_327
      | g1_pre_topc(C_328,D_327) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_314])).

tff(c_352,plain,(
    u1_pre_topc('#skF_7') = u1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_342])).

tff(c_149,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_143])).

tff(c_156,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_149])).

tff(c_40,plain,(
    ! [A_5] :
      ( r2_hidden(u1_struct_0(A_5),u1_pre_topc(A_5))
      | ~ v2_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_283,plain,
    ( r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7'))
    | ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_40])).

tff(c_298,plain,(
    r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_156,c_283])).

tff(c_356,plain,(
    r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_298])).

tff(c_68,plain,(
    ! [B_45,A_43] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_271,plain,(
    ! [B_45] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_45,'#skF_7')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_68])).

tff(c_399,plain,(
    ! [B_332] :
      ( m1_subset_1(u1_struct_0(B_332),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_332,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_271])).

tff(c_402,plain,
    ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_pre_topc('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_399])).

tff(c_417,plain,(
    ~ m1_pre_topc('#skF_7','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_423,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_417])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_423])).

tff(c_431,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_727,plain,(
    ! [B_349,A_350] :
      ( v3_pre_topc(B_349,A_350)
      | ~ r2_hidden(B_349,u1_pre_topc(A_350))
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ l1_pre_topc(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_733,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_431,c_727])).

tff(c_746,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_356,c_733])).

tff(c_1448,plain,(
    ! [B_380,A_381] :
      ( v1_tsep_1(B_380,A_381)
      | ~ v3_pre_topc(u1_struct_0(B_380),A_381)
      | ~ m1_subset_1(u1_struct_0(B_380),k1_zfmisc_1(u1_struct_0(A_381)))
      | ~ m1_pre_topc(B_380,A_381)
      | ~ l1_pre_topc(A_381)
      | ~ v2_pre_topc(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1454,plain,
    ( v1_tsep_1('#skF_6','#skF_6')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_431,c_1448])).

tff(c_1470,plain,
    ( v1_tsep_1('#skF_6','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_142,c_746,c_1454])).

tff(c_1478,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1470])).

tff(c_1484,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1478])).

tff(c_1491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1484])).

tff(c_1493,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1470])).

tff(c_462,plain,(
    ! [A_335,B_336] :
      ( m1_pre_topc(A_335,g1_pre_topc(u1_struct_0(B_336),u1_pre_topc(B_336)))
      | ~ m1_pre_topc(A_335,B_336)
      | ~ l1_pre_topc(B_336)
      | ~ l1_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_482,plain,(
    ! [A_335] :
      ( m1_pre_topc(A_335,'#skF_7')
      | ~ m1_pre_topc(A_335,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_462])).

tff(c_491,plain,(
    ! [A_335] :
      ( m1_pre_topc(A_335,'#skF_7')
      | ~ m1_pre_topc(A_335,'#skF_6')
      | ~ l1_pre_topc(A_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_482])).

tff(c_581,plain,(
    ! [A_344,B_345] :
      ( m1_pre_topc(A_344,B_345)
      | ~ m1_pre_topc(A_344,g1_pre_topc(u1_struct_0(B_345),u1_pre_topc(B_345)))
      | ~ l1_pre_topc(B_345)
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_604,plain,(
    ! [A_344] :
      ( m1_pre_topc(A_344,'#skF_6')
      | ~ m1_pre_topc(A_344,'#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_344) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_581])).

tff(c_623,plain,(
    ! [A_346] :
      ( m1_pre_topc(A_346,'#skF_6')
      | ~ m1_pre_topc(A_346,'#skF_7')
      | ~ l1_pre_topc(A_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_604])).

tff(c_641,plain,
    ( m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_623])).

tff(c_654,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_641])).

tff(c_268,plain,(
    ! [A_43] :
      ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc('#skF_7',A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_68])).

tff(c_739,plain,(
    ! [B_349] :
      ( v3_pre_topc(B_349,'#skF_7')
      | ~ r2_hidden(B_349,u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_727])).

tff(c_864,plain,(
    ! [B_355] :
      ( v3_pre_topc(B_355,'#skF_7')
      | ~ r2_hidden(B_355,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_352,c_739])).

tff(c_868,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7')
    | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_268,c_864])).

tff(c_881,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_654,c_356,c_868])).

tff(c_1581,plain,(
    ! [B_384,A_385] :
      ( v1_tsep_1(B_384,A_385)
      | ~ v3_pre_topc(u1_struct_0(B_384),A_385)
      | ~ v2_pre_topc(A_385)
      | ~ m1_pre_topc(B_384,A_385)
      | ~ l1_pre_topc(A_385) ) ),
    inference(resolution,[status(thm)],[c_68,c_1448])).

tff(c_1593,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_881,c_1581])).

tff(c_1609,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_156,c_1593])).

tff(c_1613,plain,(
    ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1609])).

tff(c_1644,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_491,c_1613])).

tff(c_1651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1493,c_1644])).

tff(c_1652,plain,(
    v1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1609])).

tff(c_1653,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1609])).

tff(c_82,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_84,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_115,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84])).

tff(c_80,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_116,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80])).

tff(c_6717,plain,(
    ! [D_533,G_535,A_536,C_537,E_534,B_538] :
      ( r1_tmap_1(D_533,B_538,E_534,G_535)
      | ~ r1_tmap_1(C_537,B_538,k3_tmap_1(A_536,B_538,D_533,C_537,E_534),G_535)
      | ~ m1_subset_1(G_535,u1_struct_0(C_537))
      | ~ m1_subset_1(G_535,u1_struct_0(D_533))
      | ~ m1_pre_topc(C_537,D_533)
      | ~ v1_tsep_1(C_537,D_533)
      | ~ m1_subset_1(E_534,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_533),u1_struct_0(B_538))))
      | ~ v1_funct_2(E_534,u1_struct_0(D_533),u1_struct_0(B_538))
      | ~ v1_funct_1(E_534)
      | ~ m1_pre_topc(D_533,A_536)
      | v2_struct_0(D_533)
      | ~ m1_pre_topc(C_537,A_536)
      | v2_struct_0(C_537)
      | ~ l1_pre_topc(B_538)
      | ~ v2_pre_topc(B_538)
      | v2_struct_0(B_538)
      | ~ l1_pre_topc(A_536)
      | ~ v2_pre_topc(A_536)
      | v2_struct_0(A_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_6719,plain,
    ( r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_7'))
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ v1_tsep_1('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_8')
    | ~ m1_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_116,c_6717])).

tff(c_6722,plain,
    ( r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_106,c_104,c_100,c_96,c_94,c_262,c_259,c_261,c_259,c_1652,c_1653,c_115,c_259,c_115,c_6719])).

tff(c_6724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_108,c_102,c_98,c_78,c_6722])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.47/2.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/2.55  
% 7.47/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/2.55  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 7.47/2.55  
% 7.47/2.55  %Foreground sorts:
% 7.47/2.55  
% 7.47/2.55  
% 7.47/2.55  %Background operators:
% 7.47/2.55  
% 7.47/2.55  
% 7.47/2.55  %Foreground operators:
% 7.47/2.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.47/2.55  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.47/2.55  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.47/2.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.47/2.55  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.47/2.55  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.47/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.47/2.55  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.47/2.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.47/2.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.47/2.55  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.47/2.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.47/2.55  tff('#skF_7', type, '#skF_7': $i).
% 7.47/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.47/2.55  tff('#skF_10', type, '#skF_10': $i).
% 7.47/2.55  tff('#skF_5', type, '#skF_5': $i).
% 7.47/2.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.47/2.55  tff('#skF_6', type, '#skF_6': $i).
% 7.47/2.55  tff('#skF_9', type, '#skF_9': $i).
% 7.47/2.55  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.47/2.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.47/2.55  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.47/2.55  tff('#skF_8', type, '#skF_8': $i).
% 7.47/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.47/2.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.47/2.55  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 7.47/2.55  tff('#skF_4', type, '#skF_4': $i).
% 7.47/2.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.47/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.47/2.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.47/2.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.47/2.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.47/2.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.47/2.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.47/2.55  
% 7.76/2.57  tff(f_251, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 7.76/2.57  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.76/2.57  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.76/2.58  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 7.76/2.58  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 7.76/2.58  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 7.76/2.58  tff(f_102, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 7.76/2.58  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.76/2.58  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 7.76/2.58  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.76/2.58  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 7.76/2.58  tff(f_129, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 7.76/2.58  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 7.76/2.58  tff(f_202, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 7.76/2.58  tff(c_114, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_108, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_102, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_98, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_78, plain, (~r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_112, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_110, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_106, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_100, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_96, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_126, plain, (![B_302, A_303]: (l1_pre_topc(B_302) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.76/2.58  tff(c_132, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_126])).
% 7.76/2.58  tff(c_139, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_132])).
% 7.76/2.58  tff(c_143, plain, (![B_304, A_305]: (v2_pre_topc(B_304) | ~m1_pre_topc(B_304, A_305) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.76/2.58  tff(c_152, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_143])).
% 7.76/2.58  tff(c_159, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_152])).
% 7.76/2.58  tff(c_135, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_126])).
% 7.76/2.58  tff(c_142, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_135])).
% 7.76/2.58  tff(c_88, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_162, plain, (![A_308]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_308), u1_pre_topc(A_308))) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.76/2.58  tff(c_165, plain, (v1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_88, c_162])).
% 7.76/2.58  tff(c_167, plain, (v1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_142, c_165])).
% 7.76/2.58  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.76/2.58  tff(c_48, plain, (![A_25]: (m1_subset_1(u1_pre_topc(A_25), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25)))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.76/2.58  tff(c_205, plain, (![C_313, A_314, D_315, B_316]: (C_313=A_314 | g1_pre_topc(C_313, D_315)!=g1_pre_topc(A_314, B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(k1_zfmisc_1(A_314))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.76/2.58  tff(c_213, plain, (![C_313, D_315]: (u1_struct_0('#skF_6')=C_313 | g1_pre_topc(C_313, D_315)!='#skF_7' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_205])).
% 7.76/2.58  tff(c_230, plain, (~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(splitLeft, [status(thm)], [c_213])).
% 7.76/2.58  tff(c_233, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_230])).
% 7.76/2.58  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_233])).
% 7.76/2.58  tff(c_240, plain, (![C_320, D_321]: (u1_struct_0('#skF_6')=C_320 | g1_pre_topc(C_320, D_321)!='#skF_7')), inference(splitRight, [status(thm)], [c_213])).
% 7.76/2.58  tff(c_250, plain, (![A_322]: (u1_struct_0(A_322)=u1_struct_0('#skF_6') | A_322!='#skF_7' | ~v1_pre_topc(A_322) | ~l1_pre_topc(A_322))), inference(superposition, [status(thm), theory('equality')], [c_2, c_240])).
% 7.76/2.58  tff(c_253, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_167, c_250])).
% 7.76/2.58  tff(c_259, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_253])).
% 7.76/2.58  tff(c_92, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_262, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_92])).
% 7.76/2.58  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_261, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_90])).
% 7.76/2.58  tff(c_70, plain, (![A_46]: (m1_pre_topc(A_46, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.76/2.58  tff(c_274, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7'))='#skF_7' | ~v1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_259, c_2])).
% 7.76/2.58  tff(c_292, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_167, c_274])).
% 7.76/2.58  tff(c_239, plain, (m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(splitRight, [status(thm)], [c_213])).
% 7.76/2.58  tff(c_306, plain, (![D_323, B_324, C_325, A_326]: (D_323=B_324 | g1_pre_topc(C_325, D_323)!=g1_pre_topc(A_326, B_324) | ~m1_subset_1(B_324, k1_zfmisc_1(k1_zfmisc_1(A_326))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.76/2.58  tff(c_314, plain, (![D_323, C_325]: (u1_pre_topc('#skF_6')=D_323 | g1_pre_topc(C_325, D_323)!='#skF_7' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_306])).
% 7.76/2.58  tff(c_342, plain, (![D_327, C_328]: (u1_pre_topc('#skF_6')=D_327 | g1_pre_topc(C_328, D_327)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_314])).
% 7.76/2.58  tff(c_352, plain, (u1_pre_topc('#skF_7')=u1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_292, c_342])).
% 7.76/2.58  tff(c_149, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_143])).
% 7.76/2.58  tff(c_156, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_149])).
% 7.76/2.58  tff(c_40, plain, (![A_5]: (r2_hidden(u1_struct_0(A_5), u1_pre_topc(A_5)) | ~v2_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.76/2.58  tff(c_283, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7')) | ~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_259, c_40])).
% 7.76/2.58  tff(c_298, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_156, c_283])).
% 7.76/2.58  tff(c_356, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_298])).
% 7.76/2.58  tff(c_68, plain, (![B_45, A_43]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.76/2.58  tff(c_271, plain, (![B_45]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_45, '#skF_7') | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_68])).
% 7.76/2.58  tff(c_399, plain, (![B_332]: (m1_subset_1(u1_struct_0(B_332), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_332, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_271])).
% 7.76/2.58  tff(c_402, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_259, c_399])).
% 7.76/2.58  tff(c_417, plain, (~m1_pre_topc('#skF_7', '#skF_7')), inference(splitLeft, [status(thm)], [c_402])).
% 7.76/2.58  tff(c_423, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_70, c_417])).
% 7.76/2.58  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_423])).
% 7.76/2.58  tff(c_431, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_402])).
% 7.76/2.58  tff(c_727, plain, (![B_349, A_350]: (v3_pre_topc(B_349, A_350) | ~r2_hidden(B_349, u1_pre_topc(A_350)) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_350))) | ~l1_pre_topc(A_350))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.76/2.58  tff(c_733, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_431, c_727])).
% 7.76/2.58  tff(c_746, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_356, c_733])).
% 7.76/2.58  tff(c_1448, plain, (![B_380, A_381]: (v1_tsep_1(B_380, A_381) | ~v3_pre_topc(u1_struct_0(B_380), A_381) | ~m1_subset_1(u1_struct_0(B_380), k1_zfmisc_1(u1_struct_0(A_381))) | ~m1_pre_topc(B_380, A_381) | ~l1_pre_topc(A_381) | ~v2_pre_topc(A_381))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.76/2.58  tff(c_1454, plain, (v1_tsep_1('#skF_6', '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_431, c_1448])).
% 7.76/2.58  tff(c_1470, plain, (v1_tsep_1('#skF_6', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_142, c_746, c_1454])).
% 7.76/2.58  tff(c_1478, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_1470])).
% 7.76/2.58  tff(c_1484, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_70, c_1478])).
% 7.76/2.58  tff(c_1491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1484])).
% 7.76/2.58  tff(c_1493, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_1470])).
% 7.76/2.58  tff(c_462, plain, (![A_335, B_336]: (m1_pre_topc(A_335, g1_pre_topc(u1_struct_0(B_336), u1_pre_topc(B_336))) | ~m1_pre_topc(A_335, B_336) | ~l1_pre_topc(B_336) | ~l1_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.76/2.58  tff(c_482, plain, (![A_335]: (m1_pre_topc(A_335, '#skF_7') | ~m1_pre_topc(A_335, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_335))), inference(superposition, [status(thm), theory('equality')], [c_88, c_462])).
% 7.76/2.58  tff(c_491, plain, (![A_335]: (m1_pre_topc(A_335, '#skF_7') | ~m1_pre_topc(A_335, '#skF_6') | ~l1_pre_topc(A_335))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_482])).
% 7.76/2.58  tff(c_581, plain, (![A_344, B_345]: (m1_pre_topc(A_344, B_345) | ~m1_pre_topc(A_344, g1_pre_topc(u1_struct_0(B_345), u1_pre_topc(B_345))) | ~l1_pre_topc(B_345) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.76/2.58  tff(c_604, plain, (![A_344]: (m1_pre_topc(A_344, '#skF_6') | ~m1_pre_topc(A_344, '#skF_7') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_344))), inference(superposition, [status(thm), theory('equality')], [c_88, c_581])).
% 7.76/2.58  tff(c_623, plain, (![A_346]: (m1_pre_topc(A_346, '#skF_6') | ~m1_pre_topc(A_346, '#skF_7') | ~l1_pre_topc(A_346))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_604])).
% 7.76/2.58  tff(c_641, plain, (m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_70, c_623])).
% 7.76/2.58  tff(c_654, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_641])).
% 7.76/2.58  tff(c_268, plain, (![A_43]: (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc('#skF_7', A_43) | ~l1_pre_topc(A_43))), inference(superposition, [status(thm), theory('equality')], [c_259, c_68])).
% 7.76/2.58  tff(c_739, plain, (![B_349]: (v3_pre_topc(B_349, '#skF_7') | ~r2_hidden(B_349, u1_pre_topc('#skF_7')) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_259, c_727])).
% 7.76/2.58  tff(c_864, plain, (![B_355]: (v3_pre_topc(B_355, '#skF_7') | ~r2_hidden(B_355, u1_pre_topc('#skF_6')) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_352, c_739])).
% 7.76/2.58  tff(c_868, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7') | ~r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_268, c_864])).
% 7.76/2.58  tff(c_881, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_654, c_356, c_868])).
% 7.76/2.58  tff(c_1581, plain, (![B_384, A_385]: (v1_tsep_1(B_384, A_385) | ~v3_pre_topc(u1_struct_0(B_384), A_385) | ~v2_pre_topc(A_385) | ~m1_pre_topc(B_384, A_385) | ~l1_pre_topc(A_385))), inference(resolution, [status(thm)], [c_68, c_1448])).
% 7.76/2.58  tff(c_1593, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~v2_pre_topc('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_881, c_1581])).
% 7.76/2.58  tff(c_1609, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_156, c_1593])).
% 7.76/2.58  tff(c_1613, plain, (~m1_pre_topc('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_1609])).
% 7.76/2.58  tff(c_1644, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_491, c_1613])).
% 7.76/2.58  tff(c_1651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1493, c_1644])).
% 7.76/2.58  tff(c_1652, plain, (v1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_1609])).
% 7.76/2.58  tff(c_1653, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_1609])).
% 7.76/2.58  tff(c_82, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_84, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_115, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_84])).
% 7.76/2.58  tff(c_80, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_251])).
% 7.76/2.58  tff(c_116, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80])).
% 7.76/2.58  tff(c_6717, plain, (![D_533, G_535, A_536, C_537, E_534, B_538]: (r1_tmap_1(D_533, B_538, E_534, G_535) | ~r1_tmap_1(C_537, B_538, k3_tmap_1(A_536, B_538, D_533, C_537, E_534), G_535) | ~m1_subset_1(G_535, u1_struct_0(C_537)) | ~m1_subset_1(G_535, u1_struct_0(D_533)) | ~m1_pre_topc(C_537, D_533) | ~v1_tsep_1(C_537, D_533) | ~m1_subset_1(E_534, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_533), u1_struct_0(B_538)))) | ~v1_funct_2(E_534, u1_struct_0(D_533), u1_struct_0(B_538)) | ~v1_funct_1(E_534) | ~m1_pre_topc(D_533, A_536) | v2_struct_0(D_533) | ~m1_pre_topc(C_537, A_536) | v2_struct_0(C_537) | ~l1_pre_topc(B_538) | ~v2_pre_topc(B_538) | v2_struct_0(B_538) | ~l1_pre_topc(A_536) | ~v2_pre_topc(A_536) | v2_struct_0(A_536))), inference(cnfTransformation, [status(thm)], [f_202])).
% 7.76/2.58  tff(c_6719, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_116, c_6717])).
% 7.76/2.58  tff(c_6722, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_106, c_104, c_100, c_96, c_94, c_262, c_259, c_261, c_259, c_1652, c_1653, c_115, c_259, c_115, c_6719])).
% 7.76/2.58  tff(c_6724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_108, c_102, c_98, c_78, c_6722])).
% 7.76/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.76/2.58  
% 7.76/2.58  Inference rules
% 7.76/2.58  ----------------------
% 7.76/2.58  #Ref     : 6
% 7.76/2.58  #Sup     : 1504
% 7.76/2.58  #Fact    : 0
% 7.76/2.58  #Define  : 0
% 7.76/2.58  #Split   : 7
% 7.76/2.58  #Chain   : 0
% 7.76/2.58  #Close   : 0
% 7.76/2.58  
% 7.76/2.58  Ordering : KBO
% 7.76/2.58  
% 7.76/2.58  Simplification rules
% 7.76/2.58  ----------------------
% 7.76/2.58  #Subsume      : 371
% 7.76/2.58  #Demod        : 3043
% 7.76/2.58  #Tautology    : 479
% 7.76/2.58  #SimpNegUnit  : 1
% 7.76/2.58  #BackRed      : 7
% 7.76/2.58  
% 7.76/2.58  #Partial instantiations: 0
% 7.76/2.58  #Strategies tried      : 1
% 7.76/2.58  
% 7.76/2.58  Timing (in seconds)
% 7.76/2.58  ----------------------
% 7.76/2.58  Preprocessing        : 0.40
% 7.76/2.58  Parsing              : 0.20
% 7.76/2.58  CNF conversion       : 0.05
% 7.76/2.58  Main loop            : 1.38
% 7.76/2.58  Inferencing          : 0.39
% 7.76/2.58  Reduction            : 0.50
% 7.76/2.58  Demodulation         : 0.37
% 7.76/2.58  BG Simplification    : 0.06
% 7.76/2.58  Subsumption          : 0.37
% 7.76/2.58  Abstraction          : 0.05
% 7.76/2.58  MUC search           : 0.00
% 7.76/2.58  Cooper               : 0.00
% 7.76/2.58  Total                : 1.83
% 7.76/2.58  Index Insertion      : 0.00
% 7.76/2.58  Index Deletion       : 0.00
% 7.76/2.58  Index Matching       : 0.00
% 7.76/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
