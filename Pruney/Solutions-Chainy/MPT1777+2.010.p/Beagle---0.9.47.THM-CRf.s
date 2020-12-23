%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:33 EST 2020

% Result     : Theorem 8.16s
% Output     : CNFRefutation 8.17s
% Verified   : 
% Statistics : Number of formulae       :  144 (2235 expanded)
%              Number of leaves         :   48 ( 768 expanded)
%              Depth                    :   18
%              Number of atoms          :  310 (12124 expanded)
%              Number of equality atoms :   30 (1701 expanded)
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

tff(f_253,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_pre_topc)).

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

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

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

tff(f_138,axiom,(
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

tff(f_131,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_204,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_108,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_102,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_78,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_112,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_110,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_106,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_100,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_96,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

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

tff(c_135,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_126])).

tff(c_142,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_135])).

tff(c_88,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_192,plain,(
    ! [A_310] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_310),u1_pre_topc(A_310)))
      | ~ l1_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_198,plain,
    ( v1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_192])).

tff(c_200,plain,
    ( v1_pre_topc('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_198])).

tff(c_201,plain,(
    v1_pre_topc('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_200])).

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

tff(c_207,plain,(
    ! [C_313,A_314,D_315,B_316] :
      ( C_313 = A_314
      | g1_pre_topc(C_313,D_315) != g1_pre_topc(A_314,B_316)
      | ~ m1_subset_1(B_316,k1_zfmisc_1(k1_zfmisc_1(A_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_215,plain,(
    ! [C_313,D_315] :
      ( u1_struct_0('#skF_6') = C_313
      | g1_pre_topc(C_313,D_315) != '#skF_7'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_207])).

tff(c_232,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_235,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_232])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_235])).

tff(c_242,plain,(
    ! [C_320,D_321] :
      ( u1_struct_0('#skF_6') = C_320
      | g1_pre_topc(C_320,D_321) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_252,plain,(
    ! [A_322] :
      ( u1_struct_0(A_322) = u1_struct_0('#skF_6')
      | A_322 != '#skF_7'
      | ~ v1_pre_topc(A_322)
      | ~ l1_pre_topc(A_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_255,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_201,c_252])).

tff(c_261,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_255])).

tff(c_92,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_264,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_92])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_263,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_90])).

tff(c_70,plain,(
    ! [A_46] :
      ( m1_pre_topc(A_46,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

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

tff(c_279,plain,
    ( g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7')) = '#skF_7'
    | ~ v1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_2])).

tff(c_297,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_201,c_279])).

tff(c_241,plain,(
    m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_310,plain,(
    ! [D_323,B_324,C_325,A_326] :
      ( D_323 = B_324
      | g1_pre_topc(C_325,D_323) != g1_pre_topc(A_326,B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(k1_zfmisc_1(A_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_318,plain,(
    ! [D_323,C_325] :
      ( u1_pre_topc('#skF_6') = D_323
      | g1_pre_topc(C_325,D_323) != '#skF_7'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_310])).

tff(c_345,plain,(
    ! [D_327,C_328] :
      ( u1_pre_topc('#skF_6') = D_327
      | g1_pre_topc(C_328,D_327) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_318])).

tff(c_355,plain,(
    u1_pre_topc('#skF_7') = u1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_345])).

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

tff(c_285,plain,
    ( r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7'))
    | ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_40])).

tff(c_302,plain,(
    r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_156,c_285])).

tff(c_359,plain,(
    r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_302])).

tff(c_68,plain,(
    ! [B_45,A_43] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_273,plain,(
    ! [B_45] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_45,'#skF_7')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_68])).

tff(c_404,plain,(
    ! [B_332] :
      ( m1_subset_1(u1_struct_0(B_332),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_332,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_273])).

tff(c_407,plain,
    ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_pre_topc('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_404])).

tff(c_422,plain,(
    ~ m1_pre_topc('#skF_7','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_428,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_422])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_428])).

tff(c_436,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_467,plain,(
    ! [B_335,A_336] :
      ( v3_pre_topc(B_335,A_336)
      | ~ r2_hidden(B_335,u1_pre_topc(A_336))
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0(A_336)))
      | ~ l1_pre_topc(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_470,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_436,c_467])).

tff(c_482,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_359,c_470])).

tff(c_1891,plain,(
    ! [B_413,A_414] :
      ( v1_tsep_1(B_413,A_414)
      | ~ v3_pre_topc(u1_struct_0(B_413),A_414)
      | ~ m1_subset_1(u1_struct_0(B_413),k1_zfmisc_1(u1_struct_0(A_414)))
      | ~ m1_pre_topc(B_413,A_414)
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1897,plain,
    ( v1_tsep_1('#skF_6','#skF_6')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_436,c_1891])).

tff(c_1913,plain,
    ( v1_tsep_1('#skF_6','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_142,c_482,c_1897])).

tff(c_1921,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1913])).

tff(c_1941,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1921])).

tff(c_1948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1941])).

tff(c_1950,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1913])).

tff(c_555,plain,(
    ! [A_341,B_342] :
      ( m1_pre_topc(A_341,g1_pre_topc(u1_struct_0(B_342),u1_pre_topc(B_342)))
      | ~ m1_pre_topc(A_341,B_342)
      | ~ l1_pre_topc(B_342)
      | ~ l1_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_575,plain,(
    ! [A_341] :
      ( m1_pre_topc(A_341,'#skF_7')
      | ~ m1_pre_topc(A_341,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_341) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_555])).

tff(c_584,plain,(
    ! [A_341] :
      ( m1_pre_topc(A_341,'#skF_7')
      | ~ m1_pre_topc(A_341,'#skF_6')
      | ~ l1_pre_topc(A_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_575])).

tff(c_476,plain,(
    ! [B_335] :
      ( v3_pre_topc(B_335,'#skF_7')
      | ~ r2_hidden(B_335,u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(B_335,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_467])).

tff(c_511,plain,(
    ! [B_339] :
      ( v3_pre_topc(B_339,'#skF_7')
      | ~ r2_hidden(B_339,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_339,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_355,c_476])).

tff(c_518,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7')
    | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(resolution,[status(thm)],[c_436,c_511])).

tff(c_531,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_518])).

tff(c_2040,plain,(
    ! [B_418,A_419] :
      ( v1_tsep_1(B_418,A_419)
      | ~ v3_pre_topc(u1_struct_0(B_418),A_419)
      | ~ v2_pre_topc(A_419)
      | ~ m1_pre_topc(B_418,A_419)
      | ~ l1_pre_topc(A_419) ) ),
    inference(resolution,[status(thm)],[c_68,c_1891])).

tff(c_2067,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_531,c_2040])).

tff(c_2094,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_156,c_2067])).

tff(c_2098,plain,(
    ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2094])).

tff(c_2112,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_584,c_2098])).

tff(c_2119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1950,c_2112])).

tff(c_2120,plain,(
    v1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2094])).

tff(c_2121,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2094])).

tff(c_82,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_84,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_115,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84])).

tff(c_80,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_116,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80])).

tff(c_7273,plain,(
    ! [A_543,C_544,G_542,D_540,E_541,B_545] :
      ( r1_tmap_1(D_540,B_545,E_541,G_542)
      | ~ r1_tmap_1(C_544,B_545,k3_tmap_1(A_543,B_545,D_540,C_544,E_541),G_542)
      | ~ m1_subset_1(G_542,u1_struct_0(C_544))
      | ~ m1_subset_1(G_542,u1_struct_0(D_540))
      | ~ m1_pre_topc(C_544,D_540)
      | ~ v1_tsep_1(C_544,D_540)
      | ~ m1_subset_1(E_541,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_540),u1_struct_0(B_545))))
      | ~ v1_funct_2(E_541,u1_struct_0(D_540),u1_struct_0(B_545))
      | ~ v1_funct_1(E_541)
      | ~ m1_pre_topc(D_540,A_543)
      | v2_struct_0(D_540)
      | ~ m1_pre_topc(C_544,A_543)
      | v2_struct_0(C_544)
      | ~ l1_pre_topc(B_545)
      | ~ v2_pre_topc(B_545)
      | v2_struct_0(B_545)
      | ~ l1_pre_topc(A_543)
      | ~ v2_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_7275,plain,
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
    inference(resolution,[status(thm)],[c_116,c_7273])).

tff(c_7278,plain,
    ( r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_106,c_104,c_100,c_96,c_94,c_264,c_261,c_263,c_261,c_2120,c_2121,c_115,c_261,c_115,c_7275])).

tff(c_7280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_108,c_102,c_98,c_78,c_7278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:13:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.16/2.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.17/2.87  
% 8.17/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.17/2.87  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 8.17/2.87  
% 8.17/2.87  %Foreground sorts:
% 8.17/2.87  
% 8.17/2.87  
% 8.17/2.87  %Background operators:
% 8.17/2.87  
% 8.17/2.87  
% 8.17/2.87  %Foreground operators:
% 8.17/2.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.17/2.87  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.17/2.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.17/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.17/2.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.17/2.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.17/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.17/2.87  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.17/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.17/2.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.17/2.87  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 8.17/2.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.17/2.87  tff('#skF_7', type, '#skF_7': $i).
% 8.17/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.17/2.87  tff('#skF_10', type, '#skF_10': $i).
% 8.17/2.87  tff('#skF_5', type, '#skF_5': $i).
% 8.17/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.17/2.87  tff('#skF_6', type, '#skF_6': $i).
% 8.17/2.87  tff('#skF_9', type, '#skF_9': $i).
% 8.17/2.87  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.17/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.17/2.87  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 8.17/2.87  tff('#skF_8', type, '#skF_8': $i).
% 8.17/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.17/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.17/2.87  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 8.17/2.87  tff('#skF_4', type, '#skF_4': $i).
% 8.17/2.87  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.17/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.17/2.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.17/2.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.17/2.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.17/2.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.17/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.17/2.87  
% 8.17/2.89  tff(f_253, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 8.17/2.89  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.17/2.89  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_pre_topc)).
% 8.17/2.89  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 8.17/2.89  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 8.17/2.89  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 8.17/2.89  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.17/2.89  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.17/2.89  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 8.17/2.89  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 8.17/2.89  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 8.17/2.89  tff(f_131, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 8.17/2.89  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 8.17/2.89  tff(f_204, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 8.17/2.89  tff(c_114, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_108, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_102, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_98, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_78, plain, (~r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_112, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_110, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_106, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_100, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_96, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_126, plain, (![B_302, A_303]: (l1_pre_topc(B_302) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.17/2.89  tff(c_132, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_126])).
% 8.17/2.89  tff(c_139, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_132])).
% 8.17/2.89  tff(c_135, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_126])).
% 8.17/2.89  tff(c_142, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_135])).
% 8.17/2.89  tff(c_88, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_192, plain, (![A_310]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_310), u1_pre_topc(A_310))) | ~l1_pre_topc(A_310) | v2_struct_0(A_310))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.17/2.89  tff(c_198, plain, (v1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_88, c_192])).
% 8.17/2.89  tff(c_200, plain, (v1_pre_topc('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_198])).
% 8.17/2.89  tff(c_201, plain, (v1_pre_topc('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_102, c_200])).
% 8.17/2.89  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.17/2.89  tff(c_48, plain, (![A_25]: (m1_subset_1(u1_pre_topc(A_25), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25)))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.17/2.89  tff(c_207, plain, (![C_313, A_314, D_315, B_316]: (C_313=A_314 | g1_pre_topc(C_313, D_315)!=g1_pre_topc(A_314, B_316) | ~m1_subset_1(B_316, k1_zfmisc_1(k1_zfmisc_1(A_314))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.17/2.89  tff(c_215, plain, (![C_313, D_315]: (u1_struct_0('#skF_6')=C_313 | g1_pre_topc(C_313, D_315)!='#skF_7' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_207])).
% 8.17/2.89  tff(c_232, plain, (~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(splitLeft, [status(thm)], [c_215])).
% 8.17/2.89  tff(c_235, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_232])).
% 8.17/2.89  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_235])).
% 8.17/2.89  tff(c_242, plain, (![C_320, D_321]: (u1_struct_0('#skF_6')=C_320 | g1_pre_topc(C_320, D_321)!='#skF_7')), inference(splitRight, [status(thm)], [c_215])).
% 8.17/2.89  tff(c_252, plain, (![A_322]: (u1_struct_0(A_322)=u1_struct_0('#skF_6') | A_322!='#skF_7' | ~v1_pre_topc(A_322) | ~l1_pre_topc(A_322))), inference(superposition, [status(thm), theory('equality')], [c_2, c_242])).
% 8.17/2.89  tff(c_255, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_201, c_252])).
% 8.17/2.89  tff(c_261, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_255])).
% 8.17/2.89  tff(c_92, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_264, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_92])).
% 8.17/2.89  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_263, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_90])).
% 8.17/2.89  tff(c_70, plain, (![A_46]: (m1_pre_topc(A_46, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.17/2.89  tff(c_143, plain, (![B_304, A_305]: (v2_pre_topc(B_304) | ~m1_pre_topc(B_304, A_305) | ~l1_pre_topc(A_305) | ~v2_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.17/2.89  tff(c_152, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_143])).
% 8.17/2.89  tff(c_159, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_152])).
% 8.17/2.89  tff(c_279, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7'))='#skF_7' | ~v1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_261, c_2])).
% 8.17/2.89  tff(c_297, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_201, c_279])).
% 8.17/2.89  tff(c_241, plain, (m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(splitRight, [status(thm)], [c_215])).
% 8.17/2.89  tff(c_310, plain, (![D_323, B_324, C_325, A_326]: (D_323=B_324 | g1_pre_topc(C_325, D_323)!=g1_pre_topc(A_326, B_324) | ~m1_subset_1(B_324, k1_zfmisc_1(k1_zfmisc_1(A_326))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.17/2.89  tff(c_318, plain, (![D_323, C_325]: (u1_pre_topc('#skF_6')=D_323 | g1_pre_topc(C_325, D_323)!='#skF_7' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_310])).
% 8.17/2.89  tff(c_345, plain, (![D_327, C_328]: (u1_pre_topc('#skF_6')=D_327 | g1_pre_topc(C_328, D_327)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_318])).
% 8.17/2.89  tff(c_355, plain, (u1_pre_topc('#skF_7')=u1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_297, c_345])).
% 8.17/2.89  tff(c_149, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_143])).
% 8.17/2.89  tff(c_156, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_149])).
% 8.17/2.89  tff(c_40, plain, (![A_5]: (r2_hidden(u1_struct_0(A_5), u1_pre_topc(A_5)) | ~v2_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.17/2.89  tff(c_285, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7')) | ~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_261, c_40])).
% 8.17/2.89  tff(c_302, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_156, c_285])).
% 8.17/2.89  tff(c_359, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_302])).
% 8.17/2.89  tff(c_68, plain, (![B_45, A_43]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.17/2.89  tff(c_273, plain, (![B_45]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_45, '#skF_7') | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_68])).
% 8.17/2.89  tff(c_404, plain, (![B_332]: (m1_subset_1(u1_struct_0(B_332), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_332, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_273])).
% 8.17/2.89  tff(c_407, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_261, c_404])).
% 8.17/2.89  tff(c_422, plain, (~m1_pre_topc('#skF_7', '#skF_7')), inference(splitLeft, [status(thm)], [c_407])).
% 8.17/2.89  tff(c_428, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_70, c_422])).
% 8.17/2.89  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_428])).
% 8.17/2.89  tff(c_436, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_407])).
% 8.17/2.89  tff(c_467, plain, (![B_335, A_336]: (v3_pre_topc(B_335, A_336) | ~r2_hidden(B_335, u1_pre_topc(A_336)) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0(A_336))) | ~l1_pre_topc(A_336))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.17/2.89  tff(c_470, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_436, c_467])).
% 8.17/2.89  tff(c_482, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_359, c_470])).
% 8.17/2.89  tff(c_1891, plain, (![B_413, A_414]: (v1_tsep_1(B_413, A_414) | ~v3_pre_topc(u1_struct_0(B_413), A_414) | ~m1_subset_1(u1_struct_0(B_413), k1_zfmisc_1(u1_struct_0(A_414))) | ~m1_pre_topc(B_413, A_414) | ~l1_pre_topc(A_414) | ~v2_pre_topc(A_414))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.17/2.89  tff(c_1897, plain, (v1_tsep_1('#skF_6', '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_436, c_1891])).
% 8.17/2.89  tff(c_1913, plain, (v1_tsep_1('#skF_6', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_142, c_482, c_1897])).
% 8.17/2.89  tff(c_1921, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_1913])).
% 8.17/2.89  tff(c_1941, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_70, c_1921])).
% 8.17/2.89  tff(c_1948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1941])).
% 8.17/2.89  tff(c_1950, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_1913])).
% 8.17/2.89  tff(c_555, plain, (![A_341, B_342]: (m1_pre_topc(A_341, g1_pre_topc(u1_struct_0(B_342), u1_pre_topc(B_342))) | ~m1_pre_topc(A_341, B_342) | ~l1_pre_topc(B_342) | ~l1_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.17/2.89  tff(c_575, plain, (![A_341]: (m1_pre_topc(A_341, '#skF_7') | ~m1_pre_topc(A_341, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_341))), inference(superposition, [status(thm), theory('equality')], [c_88, c_555])).
% 8.17/2.89  tff(c_584, plain, (![A_341]: (m1_pre_topc(A_341, '#skF_7') | ~m1_pre_topc(A_341, '#skF_6') | ~l1_pre_topc(A_341))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_575])).
% 8.17/2.89  tff(c_476, plain, (![B_335]: (v3_pre_topc(B_335, '#skF_7') | ~r2_hidden(B_335, u1_pre_topc('#skF_7')) | ~m1_subset_1(B_335, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_467])).
% 8.17/2.89  tff(c_511, plain, (![B_339]: (v3_pre_topc(B_339, '#skF_7') | ~r2_hidden(B_339, u1_pre_topc('#skF_6')) | ~m1_subset_1(B_339, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_355, c_476])).
% 8.17/2.89  tff(c_518, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7') | ~r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_436, c_511])).
% 8.17/2.89  tff(c_531, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_518])).
% 8.17/2.89  tff(c_2040, plain, (![B_418, A_419]: (v1_tsep_1(B_418, A_419) | ~v3_pre_topc(u1_struct_0(B_418), A_419) | ~v2_pre_topc(A_419) | ~m1_pre_topc(B_418, A_419) | ~l1_pre_topc(A_419))), inference(resolution, [status(thm)], [c_68, c_1891])).
% 8.17/2.89  tff(c_2067, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~v2_pre_topc('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_531, c_2040])).
% 8.17/2.89  tff(c_2094, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_156, c_2067])).
% 8.17/2.89  tff(c_2098, plain, (~m1_pre_topc('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_2094])).
% 8.17/2.89  tff(c_2112, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_584, c_2098])).
% 8.17/2.89  tff(c_2119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1950, c_2112])).
% 8.17/2.89  tff(c_2120, plain, (v1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_2094])).
% 8.17/2.89  tff(c_2121, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_2094])).
% 8.17/2.89  tff(c_82, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_84, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_115, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_84])).
% 8.17/2.89  tff(c_80, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_253])).
% 8.17/2.89  tff(c_116, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80])).
% 8.17/2.89  tff(c_7273, plain, (![A_543, C_544, G_542, D_540, E_541, B_545]: (r1_tmap_1(D_540, B_545, E_541, G_542) | ~r1_tmap_1(C_544, B_545, k3_tmap_1(A_543, B_545, D_540, C_544, E_541), G_542) | ~m1_subset_1(G_542, u1_struct_0(C_544)) | ~m1_subset_1(G_542, u1_struct_0(D_540)) | ~m1_pre_topc(C_544, D_540) | ~v1_tsep_1(C_544, D_540) | ~m1_subset_1(E_541, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_540), u1_struct_0(B_545)))) | ~v1_funct_2(E_541, u1_struct_0(D_540), u1_struct_0(B_545)) | ~v1_funct_1(E_541) | ~m1_pre_topc(D_540, A_543) | v2_struct_0(D_540) | ~m1_pre_topc(C_544, A_543) | v2_struct_0(C_544) | ~l1_pre_topc(B_545) | ~v2_pre_topc(B_545) | v2_struct_0(B_545) | ~l1_pre_topc(A_543) | ~v2_pre_topc(A_543) | v2_struct_0(A_543))), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.17/2.89  tff(c_7275, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_116, c_7273])).
% 8.17/2.89  tff(c_7278, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_106, c_104, c_100, c_96, c_94, c_264, c_261, c_263, c_261, c_2120, c_2121, c_115, c_261, c_115, c_7275])).
% 8.17/2.89  tff(c_7280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_108, c_102, c_98, c_78, c_7278])).
% 8.17/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.17/2.89  
% 8.17/2.89  Inference rules
% 8.17/2.89  ----------------------
% 8.17/2.89  #Ref     : 6
% 8.17/2.89  #Sup     : 1645
% 8.17/2.89  #Fact    : 0
% 8.17/2.89  #Define  : 0
% 8.17/2.89  #Split   : 7
% 8.17/2.89  #Chain   : 0
% 8.17/2.89  #Close   : 0
% 8.17/2.89  
% 8.17/2.89  Ordering : KBO
% 8.17/2.89  
% 8.17/2.89  Simplification rules
% 8.17/2.89  ----------------------
% 8.17/2.89  #Subsume      : 356
% 8.17/2.89  #Demod        : 3153
% 8.17/2.89  #Tautology    : 507
% 8.17/2.89  #SimpNegUnit  : 50
% 8.17/2.89  #BackRed      : 7
% 8.17/2.89  
% 8.17/2.89  #Partial instantiations: 0
% 8.17/2.89  #Strategies tried      : 1
% 8.17/2.89  
% 8.17/2.89  Timing (in seconds)
% 8.17/2.89  ----------------------
% 8.17/2.89  Preprocessing        : 0.42
% 8.17/2.89  Parsing              : 0.21
% 8.17/2.89  CNF conversion       : 0.06
% 8.17/2.90  Main loop            : 1.64
% 8.17/2.90  Inferencing          : 0.43
% 8.17/2.90  Reduction            : 0.61
% 8.17/2.90  Demodulation         : 0.47
% 8.17/2.90  BG Simplification    : 0.06
% 8.17/2.90  Subsumption          : 0.45
% 8.17/2.90  Abstraction          : 0.06
% 8.17/2.90  MUC search           : 0.00
% 8.17/2.90  Cooper               : 0.00
% 8.17/2.90  Total                : 2.11
% 8.17/2.90  Index Insertion      : 0.00
% 8.17/2.90  Index Deletion       : 0.00
% 8.17/2.90  Index Matching       : 0.00
% 8.17/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
