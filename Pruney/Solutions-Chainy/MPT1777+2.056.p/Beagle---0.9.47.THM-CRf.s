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
% DateTime   : Thu Dec  3 10:27:40 EST 2020

% Result     : Theorem 8.64s
% Output     : CNFRefutation 8.64s
% Verified   : 
% Statistics : Number of formulae       :  167 (1352 expanded)
%              Number of leaves         :   49 ( 491 expanded)
%              Depth                    :   18
%              Number of atoms          :  464 (7357 expanded)
%              Number of equality atoms :    6 ( 524 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_271,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_153,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_172,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_59,axiom,(
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

tff(f_149,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_118,axiom,(
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

tff(f_160,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_222,axiom,(
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

tff(c_110,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_100,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_126,plain,(
    ! [B_309,A_310] :
      ( l1_pre_topc(B_309)
      | ~ m1_pre_topc(B_309,A_310)
      | ~ l1_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_135,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_126])).

tff(c_142,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_135])).

tff(c_112,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_143,plain,(
    ! [B_311,A_312] :
      ( v2_pre_topc(B_311)
      | ~ m1_pre_topc(B_311,A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_152,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_143])).

tff(c_159,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_152])).

tff(c_68,plain,(
    ! [A_50] :
      ( m1_pre_topc(A_50,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_88,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_202,plain,(
    ! [B_324,A_325] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_324),u1_pre_topc(B_324)),A_325)
      | ~ m1_pre_topc(B_324,A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_221,plain,(
    ! [A_325] :
      ( m1_pre_topc('#skF_7',A_325)
      | ~ m1_pre_topc('#skF_6',A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_202])).

tff(c_96,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_149,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_143])).

tff(c_156,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_149])).

tff(c_132,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_126])).

tff(c_139,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_132])).

tff(c_537,plain,(
    ! [A_346,B_347] :
      ( m1_pre_topc(A_346,g1_pre_topc(u1_struct_0(B_347),u1_pre_topc(B_347)))
      | ~ m1_pre_topc(A_346,B_347)
      | ~ l1_pre_topc(B_347)
      | ~ l1_pre_topc(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_563,plain,(
    ! [A_346] :
      ( m1_pre_topc(A_346,'#skF_7')
      | ~ m1_pre_topc(A_346,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_346) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_537])).

tff(c_576,plain,(
    ! [A_346] :
      ( m1_pre_topc(A_346,'#skF_7')
      | ~ m1_pre_topc(A_346,'#skF_6')
      | ~ l1_pre_topc(A_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_563])).

tff(c_52,plain,(
    ! [B_32,A_30] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_32),u1_pre_topc(B_32)),A_30)
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_342,plain,(
    ! [C_333,A_334,B_335] :
      ( m1_pre_topc(C_333,A_334)
      | ~ m1_pre_topc(C_333,B_335)
      | ~ m1_pre_topc(B_335,A_334)
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_1607,plain,(
    ! [B_389,A_390,A_391] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_389),u1_pre_topc(B_389)),A_390)
      | ~ m1_pre_topc(A_391,A_390)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | ~ m1_pre_topc(B_389,A_391)
      | ~ l1_pre_topc(A_391) ) ),
    inference(resolution,[status(thm)],[c_52,c_342])).

tff(c_1627,plain,(
    ! [B_389,A_346] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_389),u1_pre_topc(B_389)),'#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | ~ m1_pre_topc(B_389,A_346)
      | ~ m1_pre_topc(A_346,'#skF_6')
      | ~ l1_pre_topc(A_346) ) ),
    inference(resolution,[status(thm)],[c_576,c_1607])).

tff(c_2129,plain,(
    ! [B_402,A_403] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_402),u1_pre_topc(B_402)),'#skF_7')
      | ~ m1_pre_topc(B_402,A_403)
      | ~ m1_pre_topc(A_403,'#skF_6')
      | ~ l1_pre_topc(A_403) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_139,c_1627])).

tff(c_2214,plain,(
    ! [A_325] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),'#skF_7')
      | ~ m1_pre_topc(A_325,'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(resolution,[status(thm)],[c_221,c_2129])).

tff(c_2287,plain,(
    ! [A_404] :
      ( ~ m1_pre_topc(A_404,'#skF_6')
      | ~ m1_pre_topc('#skF_6',A_404)
      | ~ l1_pre_topc(A_404) ) ),
    inference(splitLeft,[status(thm)],[c_2214])).

tff(c_2322,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_2287])).

tff(c_2357,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2322])).

tff(c_2375,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_2357])).

tff(c_2382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2375])).

tff(c_2383,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2214])).

tff(c_44,plain,(
    ! [B_23,A_21] :
      ( l1_pre_topc(B_23)
      | ~ m1_pre_topc(B_23,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_311,plain,(
    ! [B_331,A_332] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_331),u1_pre_topc(B_331)))
      | ~ m1_pre_topc(B_331,A_332)
      | ~ l1_pre_topc(A_332) ) ),
    inference(resolution,[status(thm)],[c_202,c_44])).

tff(c_323,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_311])).

tff(c_337,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_323])).

tff(c_50,plain,(
    ! [A_27,B_29] :
      ( m1_pre_topc(A_27,g1_pre_topc(u1_struct_0(B_29),u1_pre_topc(B_29)))
      | ~ m1_pre_topc(A_27,B_29)
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_183,plain,(
    ! [B_321,A_322] :
      ( m1_pre_topc(B_321,A_322)
      | ~ m1_pre_topc(B_321,g1_pre_topc(u1_struct_0(A_322),u1_pre_topc(A_322)))
      | ~ l1_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_858,plain,(
    ! [A_363] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_363),u1_pre_topc(A_363)),A_363)
      | ~ l1_pre_topc(A_363)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_363),u1_pre_topc(A_363))) ) ),
    inference(resolution,[status(thm)],[c_68,c_183])).

tff(c_186,plain,(
    ! [B_321] :
      ( m1_pre_topc(B_321,'#skF_6')
      | ~ m1_pre_topc(B_321,'#skF_7')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_183])).

tff(c_192,plain,(
    ! [B_321] :
      ( m1_pre_topc(B_321,'#skF_6')
      | ~ m1_pre_topc(B_321,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_186])).

tff(c_876,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),'#skF_6')
    | ~ l1_pre_topc('#skF_7')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_858,c_192])).

tff(c_902,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_139,c_876])).

tff(c_228,plain,(
    ! [B_324,A_325] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_324),u1_pre_topc(B_324)))
      | ~ m1_pre_topc(B_324,A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(resolution,[status(thm)],[c_202,c_44])).

tff(c_921,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')))))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_902,c_228])).

tff(c_945,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_921])).

tff(c_46,plain,(
    ! [B_26,A_24] :
      ( m1_pre_topc(B_26,A_24)
      | ~ m1_pre_topc(B_26,g1_pre_topc(u1_struct_0(A_24),u1_pre_topc(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12586,plain,(
    ! [B_576,A_577] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_576),u1_pre_topc(B_576)),A_577)
      | ~ l1_pre_topc(A_577)
      | ~ m1_pre_topc(B_576,g1_pre_topc(u1_struct_0(A_577),u1_pre_topc(A_577)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_577),u1_pre_topc(A_577))) ) ),
    inference(resolution,[status(thm)],[c_202,c_46])).

tff(c_12666,plain,(
    ! [A_578] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),A_578)
      | ~ l1_pre_topc(A_578)
      | ~ m1_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_578),u1_pre_topc(A_578)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_578),u1_pre_topc(A_578))) ) ),
    inference(resolution,[status(thm)],[c_221,c_12586])).

tff(c_12669,plain,(
    ! [B_29] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),B_29)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_29),u1_pre_topc(B_29)))
      | ~ m1_pre_topc('#skF_6',B_29)
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_12666])).

tff(c_12681,plain,(
    ! [B_579] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),B_579)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_579),u1_pre_topc(B_579)))
      | ~ m1_pre_topc('#skF_6',B_579)
      | ~ l1_pre_topc(B_579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_12669])).

tff(c_12693,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')))
    | ~ m1_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_945,c_12681])).

tff(c_12709,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')))
    | ~ m1_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_12693])).

tff(c_13088,plain,(
    ~ m1_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_12709])).

tff(c_13091,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_13088])).

tff(c_13097,plain,(
    ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_139,c_13091])).

tff(c_13103,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_576,c_13097])).

tff(c_13109,plain,(
    ~ m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_13103])).

tff(c_13118,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_13109])).

tff(c_13125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_13118])).

tff(c_13127,plain,(
    m1_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_12709])).

tff(c_206,plain,(
    ! [B_324] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_324),u1_pre_topc(B_324)),'#skF_6')
      | ~ m1_pre_topc(B_324,'#skF_7')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_202,c_192])).

tff(c_224,plain,(
    ! [B_324] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_324),u1_pre_topc(B_324)),'#skF_6')
      | ~ m1_pre_topc(B_324,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_206])).

tff(c_72,plain,(
    ! [C_60,A_54,B_58] :
      ( m1_pre_topc(C_60,A_54)
      | ~ m1_pre_topc(C_60,B_58)
      | ~ m1_pre_topc(B_58,A_54)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_5812,plain,(
    ! [A_475,A_476,B_477] :
      ( m1_pre_topc(A_475,A_476)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(B_477),u1_pre_topc(B_477)),A_476)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | ~ m1_pre_topc(A_475,B_477)
      | ~ l1_pre_topc(B_477)
      | ~ l1_pre_topc(A_475) ) ),
    inference(resolution,[status(thm)],[c_537,c_72])).

tff(c_5874,plain,(
    ! [A_475,B_324] :
      ( m1_pre_topc(A_475,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | ~ m1_pre_topc(A_475,B_324)
      | ~ l1_pre_topc(B_324)
      | ~ l1_pre_topc(A_475)
      | ~ m1_pre_topc(B_324,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_224,c_5812])).

tff(c_5955,plain,(
    ! [A_475,B_324] :
      ( m1_pre_topc(A_475,'#skF_6')
      | ~ m1_pre_topc(A_475,B_324)
      | ~ l1_pre_topc(B_324)
      | ~ l1_pre_topc(A_475)
      | ~ m1_pre_topc(B_324,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_142,c_5874])).

tff(c_13180,plain,
    ( m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')))
    | ~ l1_pre_topc('#skF_6')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_13127,c_5955])).

tff(c_13315,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2383,c_142,c_337,c_13180])).

tff(c_38,plain,(
    ! [A_4] :
      ( r2_hidden(u1_struct_0(A_4),u1_pre_topc(A_4))
      | ~ v2_pre_topc(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    ! [B_49,A_47] :
      ( m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_482,plain,(
    ! [B_341,A_342] :
      ( v3_pre_topc(B_341,A_342)
      | ~ r2_hidden(B_341,u1_pre_topc(A_342))
      | ~ m1_subset_1(B_341,k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ l1_pre_topc(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_837,plain,(
    ! [B_357,A_358] :
      ( v3_pre_topc(u1_struct_0(B_357),A_358)
      | ~ r2_hidden(u1_struct_0(B_357),u1_pre_topc(A_358))
      | ~ m1_pre_topc(B_357,A_358)
      | ~ l1_pre_topc(A_358) ) ),
    inference(resolution,[status(thm)],[c_66,c_482])).

tff(c_841,plain,(
    ! [A_4] :
      ( v3_pre_topc(u1_struct_0(A_4),A_4)
      | ~ m1_pre_topc(A_4,A_4)
      | ~ v2_pre_topc(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_38,c_837])).

tff(c_1380,plain,(
    ! [B_375,A_376] :
      ( v1_tsep_1(B_375,A_376)
      | ~ v3_pre_topc(u1_struct_0(B_375),A_376)
      | ~ m1_subset_1(u1_struct_0(B_375),k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ m1_pre_topc(B_375,A_376)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1385,plain,(
    ! [B_377,A_378] :
      ( v1_tsep_1(B_377,A_378)
      | ~ v3_pre_topc(u1_struct_0(B_377),A_378)
      | ~ v2_pre_topc(A_378)
      | ~ m1_pre_topc(B_377,A_378)
      | ~ l1_pre_topc(A_378) ) ),
    inference(resolution,[status(thm)],[c_66,c_1380])).

tff(c_1389,plain,(
    ! [A_4] :
      ( v1_tsep_1(A_4,A_4)
      | ~ m1_pre_topc(A_4,A_4)
      | ~ v2_pre_topc(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_841,c_1385])).

tff(c_194,plain,(
    ! [B_323] :
      ( m1_pre_topc(B_323,'#skF_6')
      | ~ m1_pre_topc(B_323,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_186])).

tff(c_198,plain,
    ( m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_194])).

tff(c_201,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_198])).

tff(c_2155,plain,(
    ! [A_346] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_346),u1_pre_topc(A_346)),'#skF_7')
      | ~ m1_pre_topc('#skF_7','#skF_6')
      | ~ l1_pre_topc('#skF_7')
      | ~ m1_pre_topc(A_346,'#skF_6')
      | ~ l1_pre_topc(A_346) ) ),
    inference(resolution,[status(thm)],[c_576,c_2129])).

tff(c_2206,plain,(
    ! [A_346] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_346),u1_pre_topc(A_346)),'#skF_7')
      | ~ m1_pre_topc(A_346,'#skF_6')
      | ~ l1_pre_topc(A_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_201,c_2155])).

tff(c_5842,plain,(
    ! [A_475,A_346] :
      ( m1_pre_topc(A_475,'#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | ~ m1_pre_topc(A_475,A_346)
      | ~ l1_pre_topc(A_475)
      | ~ m1_pre_topc(A_346,'#skF_6')
      | ~ l1_pre_topc(A_346) ) ),
    inference(resolution,[status(thm)],[c_2206,c_5812])).

tff(c_5916,plain,(
    ! [A_475,A_346] :
      ( m1_pre_topc(A_475,'#skF_7')
      | ~ m1_pre_topc(A_475,A_346)
      | ~ l1_pre_topc(A_475)
      | ~ m1_pre_topc(A_346,'#skF_6')
      | ~ l1_pre_topc(A_346) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_139,c_5842])).

tff(c_13176,plain,
    ( m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7')),'#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'),u1_pre_topc('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_13127,c_5916])).

tff(c_13309,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_902,c_142,c_13176])).

tff(c_102,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_70,plain,(
    ! [B_53,A_51] :
      ( r1_tarski(u1_struct_0(B_53),u1_struct_0(A_51))
      | ~ m1_pre_topc(B_53,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_9979,plain,(
    ! [B_536,C_537,A_538] :
      ( v1_tsep_1(B_536,C_537)
      | ~ r1_tarski(u1_struct_0(B_536),u1_struct_0(C_537))
      | ~ m1_pre_topc(C_537,A_538)
      | v2_struct_0(C_537)
      | ~ m1_pre_topc(B_536,A_538)
      | ~ v1_tsep_1(B_536,A_538)
      | ~ l1_pre_topc(A_538)
      | ~ v2_pre_topc(A_538)
      | v2_struct_0(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_14666,plain,(
    ! [B_602,A_603,A_604] :
      ( v1_tsep_1(B_602,A_603)
      | ~ m1_pre_topc(A_603,A_604)
      | v2_struct_0(A_603)
      | ~ m1_pre_topc(B_602,A_604)
      | ~ v1_tsep_1(B_602,A_604)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604)
      | ~ m1_pre_topc(B_602,A_603)
      | ~ l1_pre_topc(A_603) ) ),
    inference(resolution,[status(thm)],[c_70,c_9979])).

tff(c_14752,plain,(
    ! [B_602] :
      ( v1_tsep_1(B_602,'#skF_7')
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_602,'#skF_6')
      | ~ v1_tsep_1(B_602,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_602,'#skF_7')
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_201,c_14666])).

tff(c_14896,plain,(
    ! [B_602] :
      ( v1_tsep_1(B_602,'#skF_7')
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_602,'#skF_6')
      | ~ v1_tsep_1(B_602,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_602,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_159,c_142,c_14752])).

tff(c_15168,plain,(
    ! [B_607] :
      ( v1_tsep_1(B_607,'#skF_7')
      | ~ m1_pre_topc(B_607,'#skF_6')
      | ~ v1_tsep_1(B_607,'#skF_6')
      | ~ m1_pre_topc(B_607,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_98,c_14896])).

tff(c_114,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_108,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_78,plain,(
    ~ r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_106,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_92,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_86,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_82,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_84,plain,(
    m1_subset_1('#skF_10',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_115,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84])).

tff(c_80,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_116,plain,(
    r1_tmap_1('#skF_6','#skF_5',k3_tmap_1('#skF_4','#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80])).

tff(c_13390,plain,(
    ! [C_594,E_595,D_590,A_592,G_593,B_591] :
      ( r1_tmap_1(D_590,B_591,E_595,G_593)
      | ~ r1_tmap_1(C_594,B_591,k3_tmap_1(A_592,B_591,D_590,C_594,E_595),G_593)
      | ~ m1_subset_1(G_593,u1_struct_0(C_594))
      | ~ m1_subset_1(G_593,u1_struct_0(D_590))
      | ~ m1_pre_topc(C_594,D_590)
      | ~ v1_tsep_1(C_594,D_590)
      | ~ m1_subset_1(E_595,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_590),u1_struct_0(B_591))))
      | ~ v1_funct_2(E_595,u1_struct_0(D_590),u1_struct_0(B_591))
      | ~ v1_funct_1(E_595)
      | ~ m1_pre_topc(D_590,A_592)
      | v2_struct_0(D_590)
      | ~ m1_pre_topc(C_594,A_592)
      | v2_struct_0(C_594)
      | ~ l1_pre_topc(B_591)
      | ~ v2_pre_topc(B_591)
      | v2_struct_0(B_591)
      | ~ l1_pre_topc(A_592)
      | ~ v2_pre_topc(A_592)
      | v2_struct_0(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_13394,plain,
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
    inference(resolution,[status(thm)],[c_116,c_13390])).

tff(c_13401,plain,
    ( r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ v1_tsep_1('#skF_6','#skF_7')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_106,c_104,c_100,c_96,c_94,c_92,c_90,c_86,c_115,c_13394])).

tff(c_13402,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ v1_tsep_1('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_108,c_102,c_98,c_78,c_13401])).

tff(c_13873,plain,(
    ~ v1_tsep_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13309,c_13402])).

tff(c_15171,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ v1_tsep_1('#skF_6','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_15168,c_13873])).

tff(c_15174,plain,(
    ~ v1_tsep_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13309,c_13315,c_15171])).

tff(c_15180,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1389,c_15174])).

tff(c_15187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_159,c_13315,c_15180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.64/3.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.64/3.31  
% 8.64/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.64/3.31  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 8.64/3.31  
% 8.64/3.31  %Foreground sorts:
% 8.64/3.31  
% 8.64/3.31  
% 8.64/3.31  %Background operators:
% 8.64/3.31  
% 8.64/3.31  
% 8.64/3.31  %Foreground operators:
% 8.64/3.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.64/3.31  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.64/3.31  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.64/3.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.64/3.31  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.64/3.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.64/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.64/3.31  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.64/3.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.64/3.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.64/3.31  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 8.64/3.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.64/3.31  tff('#skF_7', type, '#skF_7': $i).
% 8.64/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.64/3.31  tff('#skF_10', type, '#skF_10': $i).
% 8.64/3.31  tff('#skF_5', type, '#skF_5': $i).
% 8.64/3.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.64/3.31  tff('#skF_6', type, '#skF_6': $i).
% 8.64/3.31  tff('#skF_9', type, '#skF_9': $i).
% 8.64/3.31  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.64/3.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.64/3.31  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 8.64/3.31  tff('#skF_8', type, '#skF_8': $i).
% 8.64/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.64/3.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.64/3.31  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 8.64/3.31  tff('#skF_4', type, '#skF_4': $i).
% 8.64/3.31  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.64/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.64/3.31  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.64/3.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.64/3.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.64/3.31  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.64/3.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.64/3.31  
% 8.64/3.34  tff(f_271, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 8.64/3.34  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.64/3.34  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.64/3.34  tff(f_153, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.64/3.34  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 8.64/3.34  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 8.64/3.34  tff(f_172, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 8.64/3.34  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 8.64/3.34  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 8.64/3.34  tff(f_149, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 8.64/3.34  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 8.64/3.34  tff(f_118, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 8.64/3.34  tff(f_160, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 8.64/3.34  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 8.64/3.34  tff(f_222, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 8.64/3.34  tff(c_110, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_100, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_126, plain, (![B_309, A_310]: (l1_pre_topc(B_309) | ~m1_pre_topc(B_309, A_310) | ~l1_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.64/3.34  tff(c_135, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_126])).
% 8.64/3.34  tff(c_142, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_135])).
% 8.64/3.34  tff(c_112, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_143, plain, (![B_311, A_312]: (v2_pre_topc(B_311) | ~m1_pre_topc(B_311, A_312) | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.64/3.34  tff(c_152, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_143])).
% 8.64/3.34  tff(c_159, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_152])).
% 8.64/3.34  tff(c_68, plain, (![A_50]: (m1_pre_topc(A_50, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_153])).
% 8.64/3.34  tff(c_88, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_202, plain, (![B_324, A_325]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_324), u1_pre_topc(B_324)), A_325) | ~m1_pre_topc(B_324, A_325) | ~l1_pre_topc(A_325))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.64/3.34  tff(c_221, plain, (![A_325]: (m1_pre_topc('#skF_7', A_325) | ~m1_pre_topc('#skF_6', A_325) | ~l1_pre_topc(A_325))), inference(superposition, [status(thm), theory('equality')], [c_88, c_202])).
% 8.64/3.34  tff(c_96, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_149, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_143])).
% 8.64/3.34  tff(c_156, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_149])).
% 8.64/3.34  tff(c_132, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_126])).
% 8.64/3.34  tff(c_139, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_132])).
% 8.64/3.34  tff(c_537, plain, (![A_346, B_347]: (m1_pre_topc(A_346, g1_pre_topc(u1_struct_0(B_347), u1_pre_topc(B_347))) | ~m1_pre_topc(A_346, B_347) | ~l1_pre_topc(B_347) | ~l1_pre_topc(A_346))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.64/3.34  tff(c_563, plain, (![A_346]: (m1_pre_topc(A_346, '#skF_7') | ~m1_pre_topc(A_346, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_346))), inference(superposition, [status(thm), theory('equality')], [c_88, c_537])).
% 8.64/3.34  tff(c_576, plain, (![A_346]: (m1_pre_topc(A_346, '#skF_7') | ~m1_pre_topc(A_346, '#skF_6') | ~l1_pre_topc(A_346))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_563])).
% 8.64/3.34  tff(c_52, plain, (![B_32, A_30]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_32), u1_pre_topc(B_32)), A_30) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.64/3.34  tff(c_342, plain, (![C_333, A_334, B_335]: (m1_pre_topc(C_333, A_334) | ~m1_pre_topc(C_333, B_335) | ~m1_pre_topc(B_335, A_334) | ~l1_pre_topc(A_334) | ~v2_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.64/3.34  tff(c_1607, plain, (![B_389, A_390, A_391]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_389), u1_pre_topc(B_389)), A_390) | ~m1_pre_topc(A_391, A_390) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | ~m1_pre_topc(B_389, A_391) | ~l1_pre_topc(A_391))), inference(resolution, [status(thm)], [c_52, c_342])).
% 8.64/3.34  tff(c_1627, plain, (![B_389, A_346]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_389), u1_pre_topc(B_389)), '#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | ~m1_pre_topc(B_389, A_346) | ~m1_pre_topc(A_346, '#skF_6') | ~l1_pre_topc(A_346))), inference(resolution, [status(thm)], [c_576, c_1607])).
% 8.64/3.34  tff(c_2129, plain, (![B_402, A_403]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_402), u1_pre_topc(B_402)), '#skF_7') | ~m1_pre_topc(B_402, A_403) | ~m1_pre_topc(A_403, '#skF_6') | ~l1_pre_topc(A_403))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_139, c_1627])).
% 8.64/3.34  tff(c_2214, plain, (![A_325]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), '#skF_7') | ~m1_pre_topc(A_325, '#skF_6') | ~m1_pre_topc('#skF_6', A_325) | ~l1_pre_topc(A_325))), inference(resolution, [status(thm)], [c_221, c_2129])).
% 8.64/3.34  tff(c_2287, plain, (![A_404]: (~m1_pre_topc(A_404, '#skF_6') | ~m1_pre_topc('#skF_6', A_404) | ~l1_pre_topc(A_404))), inference(splitLeft, [status(thm)], [c_2214])).
% 8.64/3.34  tff(c_2322, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_68, c_2287])).
% 8.64/3.34  tff(c_2357, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_2322])).
% 8.64/3.34  tff(c_2375, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_68, c_2357])).
% 8.64/3.34  tff(c_2382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_2375])).
% 8.64/3.34  tff(c_2383, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), '#skF_7')), inference(splitRight, [status(thm)], [c_2214])).
% 8.64/3.34  tff(c_44, plain, (![B_23, A_21]: (l1_pre_topc(B_23) | ~m1_pre_topc(B_23, A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.64/3.34  tff(c_311, plain, (![B_331, A_332]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_331), u1_pre_topc(B_331))) | ~m1_pre_topc(B_331, A_332) | ~l1_pre_topc(A_332))), inference(resolution, [status(thm)], [c_202, c_44])).
% 8.64/3.34  tff(c_323, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_311])).
% 8.64/3.34  tff(c_337, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_323])).
% 8.64/3.34  tff(c_50, plain, (![A_27, B_29]: (m1_pre_topc(A_27, g1_pre_topc(u1_struct_0(B_29), u1_pre_topc(B_29))) | ~m1_pre_topc(A_27, B_29) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.64/3.34  tff(c_183, plain, (![B_321, A_322]: (m1_pre_topc(B_321, A_322) | ~m1_pre_topc(B_321, g1_pre_topc(u1_struct_0(A_322), u1_pre_topc(A_322))) | ~l1_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.64/3.34  tff(c_858, plain, (![A_363]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_363), u1_pre_topc(A_363)), A_363) | ~l1_pre_topc(A_363) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_363), u1_pre_topc(A_363))))), inference(resolution, [status(thm)], [c_68, c_183])).
% 8.64/3.34  tff(c_186, plain, (![B_321]: (m1_pre_topc(B_321, '#skF_6') | ~m1_pre_topc(B_321, '#skF_7') | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_183])).
% 8.64/3.34  tff(c_192, plain, (![B_321]: (m1_pre_topc(B_321, '#skF_6') | ~m1_pre_topc(B_321, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_186])).
% 8.64/3.34  tff(c_876, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), '#skF_6') | ~l1_pre_topc('#skF_7') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')))), inference(resolution, [status(thm)], [c_858, c_192])).
% 8.64/3.34  tff(c_902, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_139, c_876])).
% 8.64/3.34  tff(c_228, plain, (![B_324, A_325]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_324), u1_pre_topc(B_324))) | ~m1_pre_topc(B_324, A_325) | ~l1_pre_topc(A_325))), inference(resolution, [status(thm)], [c_202, c_44])).
% 8.64/3.34  tff(c_921, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_902, c_228])).
% 8.64/3.34  tff(c_945, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')))))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_921])).
% 8.64/3.34  tff(c_46, plain, (![B_26, A_24]: (m1_pre_topc(B_26, A_24) | ~m1_pre_topc(B_26, g1_pre_topc(u1_struct_0(A_24), u1_pre_topc(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.64/3.34  tff(c_12586, plain, (![B_576, A_577]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_576), u1_pre_topc(B_576)), A_577) | ~l1_pre_topc(A_577) | ~m1_pre_topc(B_576, g1_pre_topc(u1_struct_0(A_577), u1_pre_topc(A_577))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_577), u1_pre_topc(A_577))))), inference(resolution, [status(thm)], [c_202, c_46])).
% 8.64/3.34  tff(c_12666, plain, (![A_578]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), A_578) | ~l1_pre_topc(A_578) | ~m1_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_578), u1_pre_topc(A_578))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_578), u1_pre_topc(A_578))))), inference(resolution, [status(thm)], [c_221, c_12586])).
% 8.64/3.34  tff(c_12669, plain, (![B_29]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), B_29) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_29), u1_pre_topc(B_29))) | ~m1_pre_topc('#skF_6', B_29) | ~l1_pre_topc(B_29) | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_50, c_12666])).
% 8.64/3.34  tff(c_12681, plain, (![B_579]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), B_579) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_579), u1_pre_topc(B_579))) | ~m1_pre_topc('#skF_6', B_579) | ~l1_pre_topc(B_579))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_12669])).
% 8.64/3.34  tff(c_12693, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))) | ~m1_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')))), inference(resolution, [status(thm)], [c_945, c_12681])).
% 8.64/3.34  tff(c_12709, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))) | ~m1_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_12693])).
% 8.64/3.34  tff(c_13088, plain, (~m1_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')))), inference(splitLeft, [status(thm)], [c_12709])).
% 8.64/3.34  tff(c_13091, plain, (~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_13088])).
% 8.64/3.34  tff(c_13097, plain, (~m1_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_139, c_13091])).
% 8.64/3.34  tff(c_13103, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_576, c_13097])).
% 8.64/3.34  tff(c_13109, plain, (~m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_13103])).
% 8.64/3.34  tff(c_13118, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_68, c_13109])).
% 8.64/3.34  tff(c_13125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_13118])).
% 8.64/3.34  tff(c_13127, plain, (m1_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')))), inference(splitRight, [status(thm)], [c_12709])).
% 8.64/3.34  tff(c_206, plain, (![B_324]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_324), u1_pre_topc(B_324)), '#skF_6') | ~m1_pre_topc(B_324, '#skF_7') | ~l1_pre_topc('#skF_7'))), inference(resolution, [status(thm)], [c_202, c_192])).
% 8.64/3.34  tff(c_224, plain, (![B_324]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_324), u1_pre_topc(B_324)), '#skF_6') | ~m1_pre_topc(B_324, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_206])).
% 8.64/3.34  tff(c_72, plain, (![C_60, A_54, B_58]: (m1_pre_topc(C_60, A_54) | ~m1_pre_topc(C_60, B_58) | ~m1_pre_topc(B_58, A_54) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.64/3.34  tff(c_5812, plain, (![A_475, A_476, B_477]: (m1_pre_topc(A_475, A_476) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(B_477), u1_pre_topc(B_477)), A_476) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | ~m1_pre_topc(A_475, B_477) | ~l1_pre_topc(B_477) | ~l1_pre_topc(A_475))), inference(resolution, [status(thm)], [c_537, c_72])).
% 8.64/3.34  tff(c_5874, plain, (![A_475, B_324]: (m1_pre_topc(A_475, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_pre_topc(A_475, B_324) | ~l1_pre_topc(B_324) | ~l1_pre_topc(A_475) | ~m1_pre_topc(B_324, '#skF_7'))), inference(resolution, [status(thm)], [c_224, c_5812])).
% 8.64/3.34  tff(c_5955, plain, (![A_475, B_324]: (m1_pre_topc(A_475, '#skF_6') | ~m1_pre_topc(A_475, B_324) | ~l1_pre_topc(B_324) | ~l1_pre_topc(A_475) | ~m1_pre_topc(B_324, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_142, c_5874])).
% 8.64/3.34  tff(c_13180, plain, (m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7'))) | ~l1_pre_topc('#skF_6') | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), '#skF_7')), inference(resolution, [status(thm)], [c_13127, c_5955])).
% 8.64/3.34  tff(c_13315, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2383, c_142, c_337, c_13180])).
% 8.64/3.34  tff(c_38, plain, (![A_4]: (r2_hidden(u1_struct_0(A_4), u1_pre_topc(A_4)) | ~v2_pre_topc(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.64/3.34  tff(c_66, plain, (![B_49, A_47]: (m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.64/3.34  tff(c_482, plain, (![B_341, A_342]: (v3_pre_topc(B_341, A_342) | ~r2_hidden(B_341, u1_pre_topc(A_342)) | ~m1_subset_1(B_341, k1_zfmisc_1(u1_struct_0(A_342))) | ~l1_pre_topc(A_342))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.64/3.34  tff(c_837, plain, (![B_357, A_358]: (v3_pre_topc(u1_struct_0(B_357), A_358) | ~r2_hidden(u1_struct_0(B_357), u1_pre_topc(A_358)) | ~m1_pre_topc(B_357, A_358) | ~l1_pre_topc(A_358))), inference(resolution, [status(thm)], [c_66, c_482])).
% 8.64/3.34  tff(c_841, plain, (![A_4]: (v3_pre_topc(u1_struct_0(A_4), A_4) | ~m1_pre_topc(A_4, A_4) | ~v2_pre_topc(A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_38, c_837])).
% 8.64/3.34  tff(c_1380, plain, (![B_375, A_376]: (v1_tsep_1(B_375, A_376) | ~v3_pre_topc(u1_struct_0(B_375), A_376) | ~m1_subset_1(u1_struct_0(B_375), k1_zfmisc_1(u1_struct_0(A_376))) | ~m1_pre_topc(B_375, A_376) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376))), inference(cnfTransformation, [status(thm)], [f_118])).
% 8.64/3.34  tff(c_1385, plain, (![B_377, A_378]: (v1_tsep_1(B_377, A_378) | ~v3_pre_topc(u1_struct_0(B_377), A_378) | ~v2_pre_topc(A_378) | ~m1_pre_topc(B_377, A_378) | ~l1_pre_topc(A_378))), inference(resolution, [status(thm)], [c_66, c_1380])).
% 8.64/3.34  tff(c_1389, plain, (![A_4]: (v1_tsep_1(A_4, A_4) | ~m1_pre_topc(A_4, A_4) | ~v2_pre_topc(A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_841, c_1385])).
% 8.64/3.34  tff(c_194, plain, (![B_323]: (m1_pre_topc(B_323, '#skF_6') | ~m1_pre_topc(B_323, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_186])).
% 8.64/3.34  tff(c_198, plain, (m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_68, c_194])).
% 8.64/3.34  tff(c_201, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_198])).
% 8.64/3.34  tff(c_2155, plain, (![A_346]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_346), u1_pre_topc(A_346)), '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_7') | ~m1_pre_topc(A_346, '#skF_6') | ~l1_pre_topc(A_346))), inference(resolution, [status(thm)], [c_576, c_2129])).
% 8.64/3.34  tff(c_2206, plain, (![A_346]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_346), u1_pre_topc(A_346)), '#skF_7') | ~m1_pre_topc(A_346, '#skF_6') | ~l1_pre_topc(A_346))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_201, c_2155])).
% 8.64/3.34  tff(c_5842, plain, (![A_475, A_346]: (m1_pre_topc(A_475, '#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | ~m1_pre_topc(A_475, A_346) | ~l1_pre_topc(A_475) | ~m1_pre_topc(A_346, '#skF_6') | ~l1_pre_topc(A_346))), inference(resolution, [status(thm)], [c_2206, c_5812])).
% 8.64/3.34  tff(c_5916, plain, (![A_475, A_346]: (m1_pre_topc(A_475, '#skF_7') | ~m1_pre_topc(A_475, A_346) | ~l1_pre_topc(A_475) | ~m1_pre_topc(A_346, '#skF_6') | ~l1_pre_topc(A_346))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_139, c_5842])).
% 8.64/3.34  tff(c_13176, plain, (m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6') | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')), '#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_7'), u1_pre_topc('#skF_7')))), inference(resolution, [status(thm)], [c_13127, c_5916])).
% 8.64/3.34  tff(c_13309, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_902, c_142, c_13176])).
% 8.64/3.34  tff(c_102, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_98, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_70, plain, (![B_53, A_51]: (r1_tarski(u1_struct_0(B_53), u1_struct_0(A_51)) | ~m1_pre_topc(B_53, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.64/3.34  tff(c_9979, plain, (![B_536, C_537, A_538]: (v1_tsep_1(B_536, C_537) | ~r1_tarski(u1_struct_0(B_536), u1_struct_0(C_537)) | ~m1_pre_topc(C_537, A_538) | v2_struct_0(C_537) | ~m1_pre_topc(B_536, A_538) | ~v1_tsep_1(B_536, A_538) | ~l1_pre_topc(A_538) | ~v2_pre_topc(A_538) | v2_struct_0(A_538))), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.64/3.34  tff(c_14666, plain, (![B_602, A_603, A_604]: (v1_tsep_1(B_602, A_603) | ~m1_pre_topc(A_603, A_604) | v2_struct_0(A_603) | ~m1_pre_topc(B_602, A_604) | ~v1_tsep_1(B_602, A_604) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604) | ~m1_pre_topc(B_602, A_603) | ~l1_pre_topc(A_603))), inference(resolution, [status(thm)], [c_70, c_9979])).
% 8.64/3.34  tff(c_14752, plain, (![B_602]: (v1_tsep_1(B_602, '#skF_7') | v2_struct_0('#skF_7') | ~m1_pre_topc(B_602, '#skF_6') | ~v1_tsep_1(B_602, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_602, '#skF_7') | ~l1_pre_topc('#skF_7'))), inference(resolution, [status(thm)], [c_201, c_14666])).
% 8.64/3.34  tff(c_14896, plain, (![B_602]: (v1_tsep_1(B_602, '#skF_7') | v2_struct_0('#skF_7') | ~m1_pre_topc(B_602, '#skF_6') | ~v1_tsep_1(B_602, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_602, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_159, c_142, c_14752])).
% 8.64/3.34  tff(c_15168, plain, (![B_607]: (v1_tsep_1(B_607, '#skF_7') | ~m1_pre_topc(B_607, '#skF_6') | ~v1_tsep_1(B_607, '#skF_6') | ~m1_pre_topc(B_607, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_102, c_98, c_14896])).
% 8.64/3.34  tff(c_114, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_108, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_78, plain, (~r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_106, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_92, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_86, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_82, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_84, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_115, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_84])).
% 8.64/3.34  tff(c_80, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_271])).
% 8.64/3.34  tff(c_116, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80])).
% 8.64/3.34  tff(c_13390, plain, (![C_594, E_595, D_590, A_592, G_593, B_591]: (r1_tmap_1(D_590, B_591, E_595, G_593) | ~r1_tmap_1(C_594, B_591, k3_tmap_1(A_592, B_591, D_590, C_594, E_595), G_593) | ~m1_subset_1(G_593, u1_struct_0(C_594)) | ~m1_subset_1(G_593, u1_struct_0(D_590)) | ~m1_pre_topc(C_594, D_590) | ~v1_tsep_1(C_594, D_590) | ~m1_subset_1(E_595, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_590), u1_struct_0(B_591)))) | ~v1_funct_2(E_595, u1_struct_0(D_590), u1_struct_0(B_591)) | ~v1_funct_1(E_595) | ~m1_pre_topc(D_590, A_592) | v2_struct_0(D_590) | ~m1_pre_topc(C_594, A_592) | v2_struct_0(C_594) | ~l1_pre_topc(B_591) | ~v2_pre_topc(B_591) | v2_struct_0(B_591) | ~l1_pre_topc(A_592) | ~v2_pre_topc(A_592) | v2_struct_0(A_592))), inference(cnfTransformation, [status(thm)], [f_222])).
% 8.64/3.34  tff(c_13394, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_116, c_13390])).
% 8.64/3.34  tff(c_13401, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7') | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_106, c_104, c_100, c_96, c_94, c_92, c_90, c_86, c_115, c_13394])).
% 8.64/3.34  tff(c_13402, plain, (~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_114, c_108, c_102, c_98, c_78, c_13401])).
% 8.64/3.34  tff(c_13873, plain, (~v1_tsep_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13309, c_13402])).
% 8.64/3.34  tff(c_15171, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~v1_tsep_1('#skF_6', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_15168, c_13873])).
% 8.64/3.34  tff(c_15174, plain, (~v1_tsep_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13309, c_13315, c_15171])).
% 8.64/3.34  tff(c_15180, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1389, c_15174])).
% 8.64/3.34  tff(c_15187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_159, c_13315, c_15180])).
% 8.64/3.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.64/3.34  
% 8.64/3.34  Inference rules
% 8.64/3.34  ----------------------
% 8.64/3.34  #Ref     : 0
% 8.64/3.34  #Sup     : 3103
% 8.64/3.34  #Fact    : 0
% 8.64/3.34  #Define  : 0
% 8.64/3.34  #Split   : 10
% 8.64/3.34  #Chain   : 0
% 8.64/3.34  #Close   : 0
% 8.64/3.34  
% 8.64/3.34  Ordering : KBO
% 8.64/3.34  
% 8.64/3.34  Simplification rules
% 8.64/3.34  ----------------------
% 8.64/3.34  #Subsume      : 1503
% 8.64/3.34  #Demod        : 4957
% 8.64/3.34  #Tautology    : 711
% 8.64/3.34  #SimpNegUnit  : 35
% 8.64/3.34  #BackRed      : 0
% 8.64/3.34  
% 8.64/3.34  #Partial instantiations: 0
% 8.64/3.34  #Strategies tried      : 1
% 8.64/3.34  
% 8.64/3.34  Timing (in seconds)
% 8.64/3.34  ----------------------
% 8.64/3.34  Preprocessing        : 0.40
% 8.64/3.34  Parsing              : 0.20
% 8.64/3.34  CNF conversion       : 0.05
% 8.64/3.34  Main loop            : 2.07
% 8.64/3.34  Inferencing          : 0.46
% 8.64/3.34  Reduction            : 0.78
% 8.64/3.34  Demodulation         : 0.60
% 8.64/3.34  BG Simplification    : 0.06
% 8.64/3.34  Subsumption          : 0.68
% 8.64/3.34  Abstraction          : 0.09
% 8.64/3.34  MUC search           : 0.00
% 8.64/3.34  Cooper               : 0.00
% 8.64/3.34  Total                : 2.53
% 8.64/3.34  Index Insertion      : 0.00
% 8.64/3.34  Index Deletion       : 0.00
% 8.64/3.34  Index Matching       : 0.00
% 8.64/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
