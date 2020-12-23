%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:33 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.48s
% Verified   : 
% Statistics : Number of formulae       :  149 (2532 expanded)
%              Number of leaves         :   48 ( 891 expanded)
%              Depth                    :   19
%              Number of atoms          :  326 (14077 expanded)
%              Number of equality atoms :   30 (2241 expanded)
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

tff(f_252,negated_conjecture,(
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

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

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

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_141,axiom,(
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

tff(f_137,axiom,(
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

tff(f_130,axiom,(
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

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_203,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_108,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_102,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_78,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_112,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_110,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_106,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_100,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_96,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_126,plain,(
    ! [B_304,A_305] :
      ( l1_pre_topc(B_304)
      | ~ m1_pre_topc(B_304,A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_132,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_126])).

tff(c_139,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_132])).

tff(c_88,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_182,plain,(
    ! [B_311,A_312] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_311),u1_pre_topc(B_311)))
      | ~ m1_pre_topc(B_311,A_312)
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_188,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_182])).

tff(c_195,plain,(
    v1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_88,c_188])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_126])).

tff(c_142,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_135])).

tff(c_48,plain,(
    ! [A_25] :
      ( m1_subset_1(u1_pre_topc(A_25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25))))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_248,plain,(
    ! [D_319,B_320,C_321,A_322] :
      ( D_319 = B_320
      | g1_pre_topc(C_321,D_319) != g1_pre_topc(A_322,B_320)
      | ~ m1_subset_1(B_320,k1_zfmisc_1(k1_zfmisc_1(A_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_256,plain,(
    ! [D_319,C_321] :
      ( u1_pre_topc('#skF_6') = D_319
      | g1_pre_topc(C_321,D_319) != '#skF_7'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_248])).

tff(c_368,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_371,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_368])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_371])).

tff(c_378,plain,(
    ! [D_334,C_335] :
      ( u1_pre_topc('#skF_6') = D_334
      | g1_pre_topc(C_335,D_334) != '#skF_7' ) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_388,plain,(
    ! [A_336] :
      ( u1_pre_topc(A_336) = u1_pre_topc('#skF_6')
      | A_336 != '#skF_7'
      | ~ v1_pre_topc(A_336)
      | ~ l1_pre_topc(A_336) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_378])).

tff(c_397,plain,
    ( u1_pre_topc('#skF_7') = u1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_195,c_388])).

tff(c_404,plain,(
    u1_pre_topc('#skF_7') = u1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_397])).

tff(c_419,plain,
    ( g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_6')) = '#skF_7'
    | ~ v1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_2])).

tff(c_433,plain,(
    g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_195,c_419])).

tff(c_377,plain,(
    m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_443,plain,(
    ! [C_337,A_338,D_339,B_340] :
      ( C_337 = A_338
      | g1_pre_topc(C_337,D_339) != g1_pre_topc(A_338,B_340)
      | ~ m1_subset_1(B_340,k1_zfmisc_1(k1_zfmisc_1(A_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_451,plain,(
    ! [C_337,D_339] :
      ( u1_struct_0('#skF_6') = C_337
      | g1_pre_topc(C_337,D_339) != '#skF_7'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_443])).

tff(c_495,plain,(
    ! [C_343,D_344] :
      ( u1_struct_0('#skF_6') = C_343
      | g1_pre_topc(C_343,D_344) != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_451])).

tff(c_505,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_495])).

tff(c_92,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_511,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_92])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_510,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_90])).

tff(c_70,plain,(
    ! [A_48] :
      ( m1_pre_topc(A_48,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_143,plain,(
    ! [B_306,A_307] :
      ( v2_pre_topc(B_306)
      | ~ m1_pre_topc(B_306,A_307)
      | ~ l1_pre_topc(A_307)
      | ~ v2_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_152,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_143])).

tff(c_159,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_152])).

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

tff(c_422,plain,
    ( r2_hidden(u1_struct_0('#skF_7'),u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_40])).

tff(c_435,plain,(
    r2_hidden(u1_struct_0('#skF_7'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_156,c_422])).

tff(c_509,plain,(
    r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_435])).

tff(c_68,plain,(
    ! [B_47,A_45] :
      ( m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_pre_topc(B_47,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_530,plain,(
    ! [B_47] :
      ( m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_47,'#skF_7')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_68])).

tff(c_656,plain,(
    ! [B_349] :
      ( m1_subset_1(u1_struct_0(B_349),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_349,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_530])).

tff(c_659,plain,
    ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_pre_topc('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_656])).

tff(c_660,plain,(
    ~ m1_pre_topc('#skF_7','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_688,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_660])).

tff(c_701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_688])).

tff(c_702,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_995,plain,(
    ! [B_368,A_369] :
      ( v3_pre_topc(B_368,A_369)
      | ~ r2_hidden(B_368,u1_pre_topc(A_369))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(u1_struct_0(A_369)))
      | ~ l1_pre_topc(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1001,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_702,c_995])).

tff(c_1014,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_509,c_1001])).

tff(c_1837,plain,(
    ! [B_399,A_400] :
      ( v1_tsep_1(B_399,A_400)
      | ~ v3_pre_topc(u1_struct_0(B_399),A_400)
      | ~ m1_subset_1(u1_struct_0(B_399),k1_zfmisc_1(u1_struct_0(A_400)))
      | ~ m1_pre_topc(B_399,A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1843,plain,
    ( v1_tsep_1('#skF_6','#skF_6')
    | ~ v3_pre_topc(u1_struct_0('#skF_6'),'#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_702,c_1837])).

tff(c_1859,plain,
    ( v1_tsep_1('#skF_6','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_142,c_1014,c_1843])).

tff(c_1867,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1859])).

tff(c_1873,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1867])).

tff(c_1880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1873])).

tff(c_1882,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1859])).

tff(c_556,plain,(
    ! [A_345,B_346] :
      ( m1_pre_topc(A_345,g1_pre_topc(u1_struct_0(B_346),u1_pre_topc(B_346)))
      | ~ m1_pre_topc(A_345,B_346)
      | ~ l1_pre_topc(B_346)
      | ~ l1_pre_topc(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_580,plain,(
    ! [A_345] :
      ( m1_pre_topc(A_345,'#skF_7')
      | ~ m1_pre_topc(A_345,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_345) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_556])).

tff(c_591,plain,(
    ! [A_345] :
      ( m1_pre_topc(A_345,'#skF_7')
      | ~ m1_pre_topc(A_345,'#skF_6')
      | ~ l1_pre_topc(A_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_580])).

tff(c_941,plain,(
    ! [A_366,B_367] :
      ( m1_pre_topc(A_366,B_367)
      | ~ m1_pre_topc(A_366,g1_pre_topc(u1_struct_0(B_367),u1_pre_topc(B_367)))
      | ~ l1_pre_topc(B_367)
      | ~ l1_pre_topc(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_972,plain,(
    ! [A_366] :
      ( m1_pre_topc(A_366,'#skF_6')
      | ~ m1_pre_topc(A_366,'#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_366) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_941])).

tff(c_1021,plain,(
    ! [A_370] :
      ( m1_pre_topc(A_370,'#skF_6')
      | ~ m1_pre_topc(A_370,'#skF_7')
      | ~ l1_pre_topc(A_370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_972])).

tff(c_1047,plain,
    ( m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_1021])).

tff(c_1066,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_1047])).

tff(c_527,plain,(
    ! [A_45] :
      ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ m1_pre_topc('#skF_7',A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_68])).

tff(c_1007,plain,(
    ! [B_368] :
      ( v3_pre_topc(B_368,'#skF_7')
      | ~ r2_hidden(B_368,u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_995])).

tff(c_1260,plain,(
    ! [B_376] :
      ( v3_pre_topc(B_376,'#skF_7')
      | ~ r2_hidden(B_376,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_404,c_1007])).

tff(c_1264,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7')
    | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_527,c_1260])).

tff(c_1277,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1066,c_509,c_1264])).

tff(c_1994,plain,(
    ! [B_403,A_404] :
      ( v1_tsep_1(B_403,A_404)
      | ~ v3_pre_topc(u1_struct_0(B_403),A_404)
      | ~ v2_pre_topc(A_404)
      | ~ m1_pre_topc(B_403,A_404)
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_68,c_1837])).

tff(c_2006,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_1277,c_1994])).

tff(c_2022,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_156,c_2006])).

tff(c_2026,plain,(
    ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2022])).

tff(c_2059,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_591,c_2026])).

tff(c_2066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1882,c_2059])).

tff(c_2067,plain,(
    v1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2022])).

tff(c_2068,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_2022])).

tff(c_82,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_84,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_115,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84])).

tff(c_80,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_116,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80])).

tff(c_7551,plain,(
    ! [G_560,C_559,D_558,B_556,E_557,A_561] :
      ( r1_tmap_1(D_558,B_556,E_557,G_560)
      | ~ r1_tmap_1(C_559,B_556,k3_tmap_1(A_561,B_556,D_558,C_559,E_557),G_560)
      | ~ m1_subset_1(G_560,u1_struct_0(C_559))
      | ~ m1_subset_1(G_560,u1_struct_0(D_558))
      | ~ m1_pre_topc(C_559,D_558)
      | ~ v1_tsep_1(C_559,D_558)
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_558),u1_struct_0(B_556))))
      | ~ v1_funct_2(E_557,u1_struct_0(D_558),u1_struct_0(B_556))
      | ~ v1_funct_1(E_557)
      | ~ m1_pre_topc(D_558,A_561)
      | v2_struct_0(D_558)
      | ~ m1_pre_topc(C_559,A_561)
      | v2_struct_0(C_559)
      | ~ l1_pre_topc(B_556)
      | ~ v2_pre_topc(B_556)
      | v2_struct_0(B_556)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561)
      | v2_struct_0(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_7553,plain,
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
    inference(resolution,[status(thm)],[c_116,c_7551])).

tff(c_7556,plain,
    ( r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_106,c_104,c_100,c_96,c_94,c_511,c_505,c_510,c_505,c_2067,c_2068,c_115,c_505,c_115,c_7553])).

tff(c_7558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_108,c_102,c_98,c_78,c_7556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.48/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/2.52  
% 7.48/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/2.53  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 7.48/2.53  
% 7.48/2.53  %Foreground sorts:
% 7.48/2.53  
% 7.48/2.53  
% 7.48/2.53  %Background operators:
% 7.48/2.53  
% 7.48/2.53  
% 7.48/2.53  %Foreground operators:
% 7.48/2.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.48/2.53  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.48/2.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.48/2.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.48/2.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.48/2.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.48/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.48/2.53  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.48/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.48/2.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.48/2.53  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.48/2.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.48/2.53  tff('#skF_7', type, '#skF_7': $i).
% 7.48/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.48/2.53  tff('#skF_10', type, '#skF_10': $i).
% 7.48/2.53  tff('#skF_5', type, '#skF_5': $i).
% 7.48/2.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.48/2.53  tff('#skF_6', type, '#skF_6': $i).
% 7.48/2.53  tff('#skF_9', type, '#skF_9': $i).
% 7.48/2.53  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.48/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.48/2.53  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.48/2.53  tff('#skF_8', type, '#skF_8': $i).
% 7.48/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.48/2.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.48/2.53  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 7.48/2.53  tff('#skF_4', type, '#skF_4': $i).
% 7.48/2.53  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.48/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.48/2.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.48/2.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.48/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.48/2.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.48/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.48/2.53  
% 7.48/2.55  tff(f_252, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 7.48/2.55  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.48/2.55  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 7.48/2.55  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 7.48/2.55  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 7.48/2.55  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 7.48/2.55  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.48/2.55  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.48/2.55  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 7.48/2.55  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.48/2.55  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 7.48/2.55  tff(f_130, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 7.48/2.55  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 7.48/2.55  tff(f_203, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 7.48/2.55  tff(c_114, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_108, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_102, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_98, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_78, plain, (~r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_112, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_110, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_106, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_100, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_96, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_126, plain, (![B_304, A_305]: (l1_pre_topc(B_304) | ~m1_pre_topc(B_304, A_305) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.48/2.55  tff(c_132, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_126])).
% 7.48/2.55  tff(c_139, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_132])).
% 7.48/2.55  tff(c_88, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_182, plain, (![B_311, A_312]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_311), u1_pre_topc(B_311))) | ~m1_pre_topc(B_311, A_312) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.48/2.55  tff(c_188, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_182])).
% 7.48/2.55  tff(c_195, plain, (v1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_88, c_188])).
% 7.48/2.55  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.48/2.55  tff(c_135, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_126])).
% 7.48/2.55  tff(c_142, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_135])).
% 7.48/2.55  tff(c_48, plain, (![A_25]: (m1_subset_1(u1_pre_topc(A_25), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_25)))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.48/2.55  tff(c_248, plain, (![D_319, B_320, C_321, A_322]: (D_319=B_320 | g1_pre_topc(C_321, D_319)!=g1_pre_topc(A_322, B_320) | ~m1_subset_1(B_320, k1_zfmisc_1(k1_zfmisc_1(A_322))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.48/2.55  tff(c_256, plain, (![D_319, C_321]: (u1_pre_topc('#skF_6')=D_319 | g1_pre_topc(C_321, D_319)!='#skF_7' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_248])).
% 7.48/2.55  tff(c_368, plain, (~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(splitLeft, [status(thm)], [c_256])).
% 7.48/2.55  tff(c_371, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_48, c_368])).
% 7.48/2.55  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_371])).
% 7.48/2.55  tff(c_378, plain, (![D_334, C_335]: (u1_pre_topc('#skF_6')=D_334 | g1_pre_topc(C_335, D_334)!='#skF_7')), inference(splitRight, [status(thm)], [c_256])).
% 7.48/2.55  tff(c_388, plain, (![A_336]: (u1_pre_topc(A_336)=u1_pre_topc('#skF_6') | A_336!='#skF_7' | ~v1_pre_topc(A_336) | ~l1_pre_topc(A_336))), inference(superposition, [status(thm), theory('equality')], [c_2, c_378])).
% 7.48/2.55  tff(c_397, plain, (u1_pre_topc('#skF_7')=u1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_195, c_388])).
% 7.48/2.55  tff(c_404, plain, (u1_pre_topc('#skF_7')=u1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_397])).
% 7.48/2.55  tff(c_419, plain, (g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_6'))='#skF_7' | ~v1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_404, c_2])).
% 7.48/2.55  tff(c_433, plain, (g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_195, c_419])).
% 7.48/2.55  tff(c_377, plain, (m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(splitRight, [status(thm)], [c_256])).
% 7.48/2.55  tff(c_443, plain, (![C_337, A_338, D_339, B_340]: (C_337=A_338 | g1_pre_topc(C_337, D_339)!=g1_pre_topc(A_338, B_340) | ~m1_subset_1(B_340, k1_zfmisc_1(k1_zfmisc_1(A_338))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.48/2.55  tff(c_451, plain, (![C_337, D_339]: (u1_struct_0('#skF_6')=C_337 | g1_pre_topc(C_337, D_339)!='#skF_7' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_443])).
% 7.48/2.55  tff(c_495, plain, (![C_343, D_344]: (u1_struct_0('#skF_6')=C_343 | g1_pre_topc(C_343, D_344)!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_377, c_451])).
% 7.48/2.55  tff(c_505, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_433, c_495])).
% 7.48/2.55  tff(c_92, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_511, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_92])).
% 7.48/2.55  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_510, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_90])).
% 7.48/2.55  tff(c_70, plain, (![A_48]: (m1_pre_topc(A_48, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.48/2.55  tff(c_143, plain, (![B_306, A_307]: (v2_pre_topc(B_306) | ~m1_pre_topc(B_306, A_307) | ~l1_pre_topc(A_307) | ~v2_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.48/2.55  tff(c_152, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_143])).
% 7.48/2.55  tff(c_159, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_152])).
% 7.48/2.55  tff(c_149, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_143])).
% 7.48/2.55  tff(c_156, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_149])).
% 7.48/2.55  tff(c_40, plain, (![A_5]: (r2_hidden(u1_struct_0(A_5), u1_pre_topc(A_5)) | ~v2_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.48/2.55  tff(c_422, plain, (r2_hidden(u1_struct_0('#skF_7'), u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_404, c_40])).
% 7.48/2.55  tff(c_435, plain, (r2_hidden(u1_struct_0('#skF_7'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_156, c_422])).
% 7.48/2.55  tff(c_509, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_435])).
% 7.48/2.55  tff(c_68, plain, (![B_47, A_45]: (m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_pre_topc(B_47, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.48/2.55  tff(c_530, plain, (![B_47]: (m1_subset_1(u1_struct_0(B_47), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_47, '#skF_7') | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_505, c_68])).
% 7.48/2.55  tff(c_656, plain, (![B_349]: (m1_subset_1(u1_struct_0(B_349), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_349, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_530])).
% 7.48/2.55  tff(c_659, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_505, c_656])).
% 7.48/2.55  tff(c_660, plain, (~m1_pre_topc('#skF_7', '#skF_7')), inference(splitLeft, [status(thm)], [c_659])).
% 7.48/2.55  tff(c_688, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_70, c_660])).
% 7.48/2.55  tff(c_701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_688])).
% 7.48/2.55  tff(c_702, plain, (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_659])).
% 7.48/2.55  tff(c_995, plain, (![B_368, A_369]: (v3_pre_topc(B_368, A_369) | ~r2_hidden(B_368, u1_pre_topc(A_369)) | ~m1_subset_1(B_368, k1_zfmisc_1(u1_struct_0(A_369))) | ~l1_pre_topc(A_369))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.48/2.55  tff(c_1001, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_702, c_995])).
% 7.48/2.55  tff(c_1014, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_509, c_1001])).
% 7.48/2.55  tff(c_1837, plain, (![B_399, A_400]: (v1_tsep_1(B_399, A_400) | ~v3_pre_topc(u1_struct_0(B_399), A_400) | ~m1_subset_1(u1_struct_0(B_399), k1_zfmisc_1(u1_struct_0(A_400))) | ~m1_pre_topc(B_399, A_400) | ~l1_pre_topc(A_400) | ~v2_pre_topc(A_400))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.48/2.55  tff(c_1843, plain, (v1_tsep_1('#skF_6', '#skF_6') | ~v3_pre_topc(u1_struct_0('#skF_6'), '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_702, c_1837])).
% 7.48/2.55  tff(c_1859, plain, (v1_tsep_1('#skF_6', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_142, c_1014, c_1843])).
% 7.48/2.55  tff(c_1867, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_1859])).
% 7.48/2.55  tff(c_1873, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_70, c_1867])).
% 7.48/2.55  tff(c_1880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1873])).
% 7.48/2.55  tff(c_1882, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_1859])).
% 7.48/2.55  tff(c_556, plain, (![A_345, B_346]: (m1_pre_topc(A_345, g1_pre_topc(u1_struct_0(B_346), u1_pre_topc(B_346))) | ~m1_pre_topc(A_345, B_346) | ~l1_pre_topc(B_346) | ~l1_pre_topc(A_345))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.48/2.55  tff(c_580, plain, (![A_345]: (m1_pre_topc(A_345, '#skF_7') | ~m1_pre_topc(A_345, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_345))), inference(superposition, [status(thm), theory('equality')], [c_88, c_556])).
% 7.48/2.55  tff(c_591, plain, (![A_345]: (m1_pre_topc(A_345, '#skF_7') | ~m1_pre_topc(A_345, '#skF_6') | ~l1_pre_topc(A_345))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_580])).
% 7.48/2.55  tff(c_941, plain, (![A_366, B_367]: (m1_pre_topc(A_366, B_367) | ~m1_pre_topc(A_366, g1_pre_topc(u1_struct_0(B_367), u1_pre_topc(B_367))) | ~l1_pre_topc(B_367) | ~l1_pre_topc(A_366))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.48/2.55  tff(c_972, plain, (![A_366]: (m1_pre_topc(A_366, '#skF_6') | ~m1_pre_topc(A_366, '#skF_7') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_366))), inference(superposition, [status(thm), theory('equality')], [c_88, c_941])).
% 7.48/2.55  tff(c_1021, plain, (![A_370]: (m1_pre_topc(A_370, '#skF_6') | ~m1_pre_topc(A_370, '#skF_7') | ~l1_pre_topc(A_370))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_972])).
% 7.48/2.55  tff(c_1047, plain, (m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_70, c_1021])).
% 7.48/2.55  tff(c_1066, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_1047])).
% 7.48/2.55  tff(c_527, plain, (![A_45]: (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_45))) | ~m1_pre_topc('#skF_7', A_45) | ~l1_pre_topc(A_45))), inference(superposition, [status(thm), theory('equality')], [c_505, c_68])).
% 7.48/2.55  tff(c_1007, plain, (![B_368]: (v3_pre_topc(B_368, '#skF_7') | ~r2_hidden(B_368, u1_pre_topc('#skF_7')) | ~m1_subset_1(B_368, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_505, c_995])).
% 7.48/2.55  tff(c_1260, plain, (![B_376]: (v3_pre_topc(B_376, '#skF_7') | ~r2_hidden(B_376, u1_pre_topc('#skF_6')) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_404, c_1007])).
% 7.48/2.55  tff(c_1264, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7') | ~r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6')) | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_527, c_1260])).
% 7.48/2.55  tff(c_1277, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_1066, c_509, c_1264])).
% 7.48/2.55  tff(c_1994, plain, (![B_403, A_404]: (v1_tsep_1(B_403, A_404) | ~v3_pre_topc(u1_struct_0(B_403), A_404) | ~v2_pre_topc(A_404) | ~m1_pre_topc(B_403, A_404) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_68, c_1837])).
% 7.48/2.55  tff(c_2006, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~v2_pre_topc('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_1277, c_1994])).
% 7.48/2.55  tff(c_2022, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_156, c_2006])).
% 7.48/2.55  tff(c_2026, plain, (~m1_pre_topc('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_2022])).
% 7.48/2.55  tff(c_2059, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_591, c_2026])).
% 7.48/2.55  tff(c_2066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1882, c_2059])).
% 7.48/2.55  tff(c_2067, plain, (v1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_2022])).
% 7.48/2.55  tff(c_2068, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_2022])).
% 7.48/2.55  tff(c_82, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_84, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_115, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_84])).
% 7.48/2.55  tff(c_80, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_252])).
% 7.48/2.55  tff(c_116, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80])).
% 7.48/2.55  tff(c_7551, plain, (![G_560, C_559, D_558, B_556, E_557, A_561]: (r1_tmap_1(D_558, B_556, E_557, G_560) | ~r1_tmap_1(C_559, B_556, k3_tmap_1(A_561, B_556, D_558, C_559, E_557), G_560) | ~m1_subset_1(G_560, u1_struct_0(C_559)) | ~m1_subset_1(G_560, u1_struct_0(D_558)) | ~m1_pre_topc(C_559, D_558) | ~v1_tsep_1(C_559, D_558) | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_558), u1_struct_0(B_556)))) | ~v1_funct_2(E_557, u1_struct_0(D_558), u1_struct_0(B_556)) | ~v1_funct_1(E_557) | ~m1_pre_topc(D_558, A_561) | v2_struct_0(D_558) | ~m1_pre_topc(C_559, A_561) | v2_struct_0(C_559) | ~l1_pre_topc(B_556) | ~v2_pre_topc(B_556) | v2_struct_0(B_556) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561) | v2_struct_0(A_561))), inference(cnfTransformation, [status(thm)], [f_203])).
% 7.48/2.55  tff(c_7553, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_116, c_7551])).
% 7.48/2.55  tff(c_7556, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_106, c_104, c_100, c_96, c_94, c_511, c_505, c_510, c_505, c_2067, c_2068, c_115, c_505, c_115, c_7553])).
% 7.48/2.55  tff(c_7558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_108, c_102, c_98, c_78, c_7556])).
% 7.48/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.48/2.55  
% 7.48/2.55  Inference rules
% 7.48/2.55  ----------------------
% 7.48/2.55  #Ref     : 6
% 7.48/2.55  #Sup     : 1524
% 7.48/2.55  #Fact    : 0
% 7.48/2.55  #Define  : 0
% 7.48/2.55  #Split   : 7
% 7.48/2.55  #Chain   : 0
% 7.48/2.55  #Close   : 0
% 7.48/2.55  
% 7.48/2.55  Ordering : KBO
% 7.48/2.55  
% 7.48/2.55  Simplification rules
% 7.48/2.55  ----------------------
% 7.48/2.55  #Subsume      : 481
% 7.48/2.55  #Demod        : 4138
% 7.48/2.55  #Tautology    : 608
% 7.48/2.55  #SimpNegUnit  : 1
% 7.48/2.55  #BackRed      : 9
% 7.48/2.55  
% 7.48/2.55  #Partial instantiations: 0
% 7.48/2.55  #Strategies tried      : 1
% 7.48/2.55  
% 7.48/2.55  Timing (in seconds)
% 7.48/2.55  ----------------------
% 7.48/2.55  Preprocessing        : 0.41
% 7.48/2.55  Parsing              : 0.21
% 7.48/2.55  CNF conversion       : 0.05
% 7.48/2.56  Main loop            : 1.36
% 7.48/2.56  Inferencing          : 0.39
% 7.48/2.56  Reduction            : 0.52
% 7.48/2.56  Demodulation         : 0.39
% 7.48/2.56  BG Simplification    : 0.05
% 7.48/2.56  Subsumption          : 0.33
% 7.48/2.56  Abstraction          : 0.05
% 7.48/2.56  MUC search           : 0.00
% 7.48/2.56  Cooper               : 0.00
% 7.48/2.56  Total                : 1.81
% 7.48/2.56  Index Insertion      : 0.00
% 7.48/2.56  Index Deletion       : 0.00
% 7.48/2.56  Index Matching       : 0.00
% 7.48/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
