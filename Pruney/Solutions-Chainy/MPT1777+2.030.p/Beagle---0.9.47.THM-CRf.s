%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:36 EST 2020

% Result     : Theorem 6.44s
% Output     : CNFRefutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :  126 (1340 expanded)
%              Number of leaves         :   46 ( 497 expanded)
%              Depth                    :   18
%              Number of atoms          :  299 (7808 expanded)
%              Number of equality atoms :   12 ( 660 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_140,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_115,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

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

tff(c_128,plain,(
    ! [B_306,A_307] :
      ( l1_pre_topc(B_306)
      | ~ m1_pre_topc(B_306,A_307)
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_137,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_128])).

tff(c_144,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_137])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_393,plain,(
    ! [B_333,C_334,A_335] :
      ( m1_pre_topc(B_333,C_334)
      | ~ r1_tarski(u1_struct_0(B_333),u1_struct_0(C_334))
      | ~ m1_pre_topc(C_334,A_335)
      | ~ m1_pre_topc(B_333,A_335)
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_433,plain,(
    ! [B_337,A_338] :
      ( m1_pre_topc(B_337,B_337)
      | ~ m1_pre_topc(B_337,A_338)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338) ) ),
    inference(resolution,[status(thm)],[c_6,c_393])).

tff(c_451,plain,
    ( m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_433])).

tff(c_468,plain,(
    m1_pre_topc('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_451])).

tff(c_88,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_338,plain,(
    ! [A_330,B_331] :
      ( m1_pre_topc(A_330,g1_pre_topc(u1_struct_0(B_331),u1_pre_topc(B_331)))
      | ~ m1_pre_topc(A_330,B_331)
      | ~ l1_pre_topc(B_331)
      | ~ l1_pre_topc(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_354,plain,(
    ! [A_330] :
      ( m1_pre_topc(A_330,'#skF_7')
      | ~ m1_pre_topc(A_330,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_338])).

tff(c_361,plain,(
    ! [A_330] :
      ( m1_pre_topc(A_330,'#skF_7')
      | ~ m1_pre_topc(A_330,'#skF_6')
      | ~ l1_pre_topc(A_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_354])).

tff(c_134,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_128])).

tff(c_141,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_134])).

tff(c_66,plain,(
    ! [A_42] :
      ( m1_pre_topc(A_42,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_171,plain,(
    ! [B_315,A_316] :
      ( m1_pre_topc(B_315,A_316)
      | ~ m1_pre_topc(B_315,g1_pre_topc(u1_struct_0(A_316),u1_pre_topc(A_316)))
      | ~ l1_pre_topc(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_174,plain,(
    ! [B_315] :
      ( m1_pre_topc(B_315,'#skF_6')
      | ~ m1_pre_topc(B_315,'#skF_7')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_171])).

tff(c_182,plain,(
    ! [B_317] :
      ( m1_pre_topc(B_317,'#skF_6')
      | ~ m1_pre_topc(B_317,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_174])).

tff(c_186,plain,
    ( m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_182])).

tff(c_189,plain,(
    m1_pre_topc('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_186])).

tff(c_153,plain,(
    ! [B_311,A_312] :
      ( v2_pre_topc(B_311)
      | ~ m1_pre_topc(B_311,A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_162,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_153])).

tff(c_169,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_162])).

tff(c_535,plain,(
    ! [B_339,C_340,A_341] :
      ( r1_tarski(u1_struct_0(B_339),u1_struct_0(C_340))
      | ~ m1_pre_topc(B_339,C_340)
      | ~ m1_pre_topc(C_340,A_341)
      | ~ m1_pre_topc(B_339,A_341)
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_537,plain,(
    ! [B_339] :
      ( r1_tarski(u1_struct_0(B_339),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_339,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_468,c_535])).

tff(c_560,plain,(
    ! [B_339] :
      ( r1_tarski(u1_struct_0(B_339),u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(B_339,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_144,c_537])).

tff(c_159,plain,
    ( v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_153])).

tff(c_166,plain,(
    v2_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_159])).

tff(c_449,plain,
    ( m1_pre_topc('#skF_7','#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_433])).

tff(c_465,plain,(
    m1_pre_topc('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_449])).

tff(c_539,plain,(
    ! [B_339] :
      ( r1_tarski(u1_struct_0(B_339),u1_struct_0('#skF_7'))
      | ~ m1_pre_topc(B_339,'#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_465,c_535])).

tff(c_588,plain,(
    ! [B_343] :
      ( r1_tarski(u1_struct_0(B_343),u1_struct_0('#skF_7'))
      | ~ m1_pre_topc(B_343,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_141,c_539])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_602,plain,(
    ! [B_346] :
      ( u1_struct_0(B_346) = u1_struct_0('#skF_7')
      | ~ r1_tarski(u1_struct_0('#skF_7'),u1_struct_0(B_346))
      | ~ m1_pre_topc(B_346,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_588,c_2])).

tff(c_614,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_560,c_602])).

tff(c_626,plain,
    ( u1_struct_0('#skF_7') = u1_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_614])).

tff(c_631,plain,(
    ~ m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_626])).

tff(c_634,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_361,c_631])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_468,c_634])).

tff(c_642,plain,(
    u1_struct_0('#skF_7') = u1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_92,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_7'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_687,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_92])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_686,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_90])).

tff(c_643,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_44,plain,(
    ! [A_6] :
      ( r2_hidden(u1_struct_0(A_6),u1_pre_topc(A_6))
      | ~ v2_pre_topc(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_727,plain,
    ( r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7'))
    | ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_44])).

tff(c_747,plain,(
    r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_166,c_727])).

tff(c_64,plain,(
    ! [B_41,A_39] :
      ( m1_subset_1(u1_struct_0(B_41),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_721,plain,(
    ! [A_39] :
      ( m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_pre_topc('#skF_7',A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_64])).

tff(c_46,plain,(
    ! [B_22,A_20] :
      ( v3_pre_topc(B_22,A_20)
      | ~ r2_hidden(B_22,u1_pre_topc(A_20))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_715,plain,(
    ! [B_22] :
      ( v3_pre_topc(B_22,'#skF_7')
      | ~ r2_hidden(B_22,u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_46])).

tff(c_1089,plain,(
    ! [B_360] :
      ( v3_pre_topc(B_360,'#skF_7')
      | ~ r2_hidden(B_360,u1_pre_topc('#skF_7'))
      | ~ m1_subset_1(B_360,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_715])).

tff(c_1093,plain,
    ( v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7')
    | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_7'))
    | ~ m1_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_721,c_1089])).

tff(c_1110,plain,(
    v3_pre_topc(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_189,c_747,c_1093])).

tff(c_1122,plain,(
    ! [B_361,A_362] :
      ( v1_tsep_1(B_361,A_362)
      | ~ v3_pre_topc(u1_struct_0(B_361),A_362)
      | ~ m1_subset_1(u1_struct_0(B_361),k1_zfmisc_1(u1_struct_0(A_362)))
      | ~ m1_pre_topc(B_361,A_362)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1452,plain,(
    ! [B_377,A_378] :
      ( v1_tsep_1(B_377,A_378)
      | ~ v3_pre_topc(u1_struct_0(B_377),A_378)
      | ~ v2_pre_topc(A_378)
      | ~ m1_pre_topc(B_377,A_378)
      | ~ l1_pre_topc(A_378) ) ),
    inference(resolution,[status(thm)],[c_64,c_1122])).

tff(c_1458,plain,
    ( v1_tsep_1('#skF_6','#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_1110,c_1452])).

tff(c_1468,plain,(
    v1_tsep_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_643,c_166,c_1458])).

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

tff(c_5447,plain,(
    ! [B_521,E_519,G_520,D_522,C_523,A_524] :
      ( r1_tmap_1(D_522,B_521,E_519,G_520)
      | ~ r1_tmap_1(C_523,B_521,k3_tmap_1(A_524,B_521,D_522,C_523,E_519),G_520)
      | ~ m1_subset_1(G_520,u1_struct_0(C_523))
      | ~ m1_subset_1(G_520,u1_struct_0(D_522))
      | ~ m1_pre_topc(C_523,D_522)
      | ~ v1_tsep_1(C_523,D_522)
      | ~ m1_subset_1(E_519,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_522),u1_struct_0(B_521))))
      | ~ v1_funct_2(E_519,u1_struct_0(D_522),u1_struct_0(B_521))
      | ~ v1_funct_1(E_519)
      | ~ m1_pre_topc(D_522,A_524)
      | v2_struct_0(D_522)
      | ~ m1_pre_topc(C_523,A_524)
      | v2_struct_0(C_523)
      | ~ l1_pre_topc(B_521)
      | ~ v2_pre_topc(B_521)
      | v2_struct_0(B_521)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_5449,plain,
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
    inference(resolution,[status(thm)],[c_116,c_5447])).

tff(c_5452,plain,
    ( r1_tmap_1('#skF_7','#skF_5','#skF_8','#skF_9')
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_110,c_106,c_104,c_100,c_96,c_94,c_687,c_642,c_686,c_642,c_1468,c_643,c_115,c_642,c_115,c_5449])).

tff(c_5454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_108,c_102,c_98,c_78,c_5452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.44/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.44/2.29  
% 6.44/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.44/2.29  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k9_subset_1 > k5_setfam_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3
% 6.44/2.29  
% 6.44/2.29  %Foreground sorts:
% 6.44/2.29  
% 6.44/2.29  
% 6.44/2.29  %Background operators:
% 6.44/2.29  
% 6.44/2.29  
% 6.44/2.29  %Foreground operators:
% 6.44/2.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.44/2.29  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.44/2.29  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.44/2.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.44/2.29  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.44/2.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.44/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.44/2.29  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.44/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.44/2.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.44/2.29  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 6.44/2.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.71/2.29  tff('#skF_7', type, '#skF_7': $i).
% 6.71/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.71/2.29  tff('#skF_10', type, '#skF_10': $i).
% 6.71/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.71/2.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.71/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.71/2.29  tff('#skF_9', type, '#skF_9': $i).
% 6.71/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.71/2.29  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 6.71/2.29  tff('#skF_8', type, '#skF_8': $i).
% 6.71/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.71/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.71/2.29  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.71/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.71/2.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.71/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.71/2.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.71/2.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.71/2.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.71/2.29  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.71/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.71/2.29  
% 6.71/2.31  tff(f_251, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 6.71/2.31  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.71/2.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.71/2.31  tff(f_140, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.71/2.31  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 6.71/2.31  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.71/2.31  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.71/2.31  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.71/2.31  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 6.71/2.31  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.71/2.31  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 6.71/2.31  tff(f_115, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 6.71/2.31  tff(f_202, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 6.71/2.31  tff(c_114, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_108, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_102, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_98, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_78, plain, (~r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_112, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_110, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_106, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_100, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_96, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_128, plain, (![B_306, A_307]: (l1_pre_topc(B_306) | ~m1_pre_topc(B_306, A_307) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.71/2.31  tff(c_137, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_128])).
% 6.71/2.31  tff(c_144, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_137])).
% 6.71/2.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.71/2.31  tff(c_393, plain, (![B_333, C_334, A_335]: (m1_pre_topc(B_333, C_334) | ~r1_tarski(u1_struct_0(B_333), u1_struct_0(C_334)) | ~m1_pre_topc(C_334, A_335) | ~m1_pre_topc(B_333, A_335) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.71/2.31  tff(c_433, plain, (![B_337, A_338]: (m1_pre_topc(B_337, B_337) | ~m1_pre_topc(B_337, A_338) | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338))), inference(resolution, [status(thm)], [c_6, c_393])).
% 6.71/2.31  tff(c_451, plain, (m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_433])).
% 6.71/2.31  tff(c_468, plain, (m1_pre_topc('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_451])).
% 6.71/2.31  tff(c_88, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_338, plain, (![A_330, B_331]: (m1_pre_topc(A_330, g1_pre_topc(u1_struct_0(B_331), u1_pre_topc(B_331))) | ~m1_pre_topc(A_330, B_331) | ~l1_pre_topc(B_331) | ~l1_pre_topc(A_330))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.71/2.31  tff(c_354, plain, (![A_330]: (m1_pre_topc(A_330, '#skF_7') | ~m1_pre_topc(A_330, '#skF_6') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc(A_330))), inference(superposition, [status(thm), theory('equality')], [c_88, c_338])).
% 6.71/2.31  tff(c_361, plain, (![A_330]: (m1_pre_topc(A_330, '#skF_7') | ~m1_pre_topc(A_330, '#skF_6') | ~l1_pre_topc(A_330))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_354])).
% 6.71/2.31  tff(c_134, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_128])).
% 6.71/2.31  tff(c_141, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_134])).
% 6.71/2.31  tff(c_66, plain, (![A_42]: (m1_pre_topc(A_42, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.71/2.31  tff(c_171, plain, (![B_315, A_316]: (m1_pre_topc(B_315, A_316) | ~m1_pre_topc(B_315, g1_pre_topc(u1_struct_0(A_316), u1_pre_topc(A_316))) | ~l1_pre_topc(A_316))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.71/2.31  tff(c_174, plain, (![B_315]: (m1_pre_topc(B_315, '#skF_6') | ~m1_pre_topc(B_315, '#skF_7') | ~l1_pre_topc('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_171])).
% 6.71/2.31  tff(c_182, plain, (![B_317]: (m1_pre_topc(B_317, '#skF_6') | ~m1_pre_topc(B_317, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_174])).
% 6.71/2.31  tff(c_186, plain, (m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_66, c_182])).
% 6.71/2.31  tff(c_189, plain, (m1_pre_topc('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_186])).
% 6.71/2.31  tff(c_153, plain, (![B_311, A_312]: (v2_pre_topc(B_311) | ~m1_pre_topc(B_311, A_312) | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.71/2.31  tff(c_162, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_100, c_153])).
% 6.71/2.31  tff(c_169, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_162])).
% 6.71/2.31  tff(c_535, plain, (![B_339, C_340, A_341]: (r1_tarski(u1_struct_0(B_339), u1_struct_0(C_340)) | ~m1_pre_topc(B_339, C_340) | ~m1_pre_topc(C_340, A_341) | ~m1_pre_topc(B_339, A_341) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.71/2.31  tff(c_537, plain, (![B_339]: (r1_tarski(u1_struct_0(B_339), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_339, '#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_468, c_535])).
% 6.71/2.31  tff(c_560, plain, (![B_339]: (r1_tarski(u1_struct_0(B_339), u1_struct_0('#skF_6')) | ~m1_pre_topc(B_339, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_144, c_537])).
% 6.71/2.31  tff(c_159, plain, (v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_153])).
% 6.71/2.31  tff(c_166, plain, (v2_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_159])).
% 6.71/2.31  tff(c_449, plain, (m1_pre_topc('#skF_7', '#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_433])).
% 6.71/2.31  tff(c_465, plain, (m1_pre_topc('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_449])).
% 6.71/2.31  tff(c_539, plain, (![B_339]: (r1_tarski(u1_struct_0(B_339), u1_struct_0('#skF_7')) | ~m1_pre_topc(B_339, '#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7'))), inference(resolution, [status(thm)], [c_465, c_535])).
% 6.71/2.31  tff(c_588, plain, (![B_343]: (r1_tarski(u1_struct_0(B_343), u1_struct_0('#skF_7')) | ~m1_pre_topc(B_343, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_141, c_539])).
% 6.71/2.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.71/2.31  tff(c_602, plain, (![B_346]: (u1_struct_0(B_346)=u1_struct_0('#skF_7') | ~r1_tarski(u1_struct_0('#skF_7'), u1_struct_0(B_346)) | ~m1_pre_topc(B_346, '#skF_7'))), inference(resolution, [status(thm)], [c_588, c_2])).
% 6.71/2.31  tff(c_614, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6') | ~m1_pre_topc('#skF_6', '#skF_7') | ~m1_pre_topc('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_560, c_602])).
% 6.71/2.31  tff(c_626, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6') | ~m1_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_614])).
% 6.71/2.31  tff(c_631, plain, (~m1_pre_topc('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_626])).
% 6.71/2.31  tff(c_634, plain, (~m1_pre_topc('#skF_6', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_361, c_631])).
% 6.71/2.31  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_468, c_634])).
% 6.71/2.31  tff(c_642, plain, (u1_struct_0('#skF_7')=u1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_626])).
% 6.71/2.31  tff(c_92, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_687, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_642, c_92])).
% 6.71/2.31  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_686, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_642, c_90])).
% 6.71/2.31  tff(c_643, plain, (m1_pre_topc('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_626])).
% 6.71/2.31  tff(c_44, plain, (![A_6]: (r2_hidden(u1_struct_0(A_6), u1_pre_topc(A_6)) | ~v2_pre_topc(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.71/2.31  tff(c_727, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7')) | ~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_642, c_44])).
% 6.71/2.31  tff(c_747, plain, (r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_166, c_727])).
% 6.71/2.31  tff(c_64, plain, (![B_41, A_39]: (m1_subset_1(u1_struct_0(B_41), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_pre_topc(B_41, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.71/2.31  tff(c_721, plain, (![A_39]: (m1_subset_1(u1_struct_0('#skF_6'), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_pre_topc('#skF_7', A_39) | ~l1_pre_topc(A_39))), inference(superposition, [status(thm), theory('equality')], [c_642, c_64])).
% 6.71/2.31  tff(c_46, plain, (![B_22, A_20]: (v3_pre_topc(B_22, A_20) | ~r2_hidden(B_22, u1_pre_topc(A_20)) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.71/2.31  tff(c_715, plain, (![B_22]: (v3_pre_topc(B_22, '#skF_7') | ~r2_hidden(B_22, u1_pre_topc('#skF_7')) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_642, c_46])).
% 6.71/2.31  tff(c_1089, plain, (![B_360]: (v3_pre_topc(B_360, '#skF_7') | ~r2_hidden(B_360, u1_pre_topc('#skF_7')) | ~m1_subset_1(B_360, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_715])).
% 6.71/2.31  tff(c_1093, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7') | ~r2_hidden(u1_struct_0('#skF_6'), u1_pre_topc('#skF_7')) | ~m1_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_721, c_1089])).
% 6.71/2.31  tff(c_1110, plain, (v3_pre_topc(u1_struct_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_189, c_747, c_1093])).
% 6.71/2.31  tff(c_1122, plain, (![B_361, A_362]: (v1_tsep_1(B_361, A_362) | ~v3_pre_topc(u1_struct_0(B_361), A_362) | ~m1_subset_1(u1_struct_0(B_361), k1_zfmisc_1(u1_struct_0(A_362))) | ~m1_pre_topc(B_361, A_362) | ~l1_pre_topc(A_362) | ~v2_pre_topc(A_362))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.71/2.31  tff(c_1452, plain, (![B_377, A_378]: (v1_tsep_1(B_377, A_378) | ~v3_pre_topc(u1_struct_0(B_377), A_378) | ~v2_pre_topc(A_378) | ~m1_pre_topc(B_377, A_378) | ~l1_pre_topc(A_378))), inference(resolution, [status(thm)], [c_64, c_1122])).
% 6.71/2.31  tff(c_1458, plain, (v1_tsep_1('#skF_6', '#skF_7') | ~v2_pre_topc('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_1110, c_1452])).
% 6.71/2.31  tff(c_1468, plain, (v1_tsep_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_643, c_166, c_1458])).
% 6.71/2.31  tff(c_82, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_84, plain, (m1_subset_1('#skF_10', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_115, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_84])).
% 6.71/2.31  tff(c_80, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_251])).
% 6.71/2.31  tff(c_116, plain, (r1_tmap_1('#skF_6', '#skF_5', k3_tmap_1('#skF_4', '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80])).
% 6.71/2.31  tff(c_5447, plain, (![B_521, E_519, G_520, D_522, C_523, A_524]: (r1_tmap_1(D_522, B_521, E_519, G_520) | ~r1_tmap_1(C_523, B_521, k3_tmap_1(A_524, B_521, D_522, C_523, E_519), G_520) | ~m1_subset_1(G_520, u1_struct_0(C_523)) | ~m1_subset_1(G_520, u1_struct_0(D_522)) | ~m1_pre_topc(C_523, D_522) | ~v1_tsep_1(C_523, D_522) | ~m1_subset_1(E_519, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_522), u1_struct_0(B_521)))) | ~v1_funct_2(E_519, u1_struct_0(D_522), u1_struct_0(B_521)) | ~v1_funct_1(E_519) | ~m1_pre_topc(D_522, A_524) | v2_struct_0(D_522) | ~m1_pre_topc(C_523, A_524) | v2_struct_0(C_523) | ~l1_pre_topc(B_521) | ~v2_pre_topc(B_521) | v2_struct_0(B_521) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.71/2.31  tff(c_5449, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_9', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_7')) | ~m1_pre_topc('#skF_6', '#skF_7') | ~v1_tsep_1('#skF_6', '#skF_7') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_8', u1_struct_0('#skF_7'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_8') | ~m1_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_116, c_5447])).
% 6.71/2.31  tff(c_5452, plain, (r1_tmap_1('#skF_7', '#skF_5', '#skF_8', '#skF_9') | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_110, c_106, c_104, c_100, c_96, c_94, c_687, c_642, c_686, c_642, c_1468, c_643, c_115, c_642, c_115, c_5449])).
% 6.71/2.31  tff(c_5454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_108, c_102, c_98, c_78, c_5452])).
% 6.71/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.31  
% 6.71/2.31  Inference rules
% 6.71/2.31  ----------------------
% 6.71/2.31  #Ref     : 0
% 6.71/2.31  #Sup     : 1037
% 6.71/2.31  #Fact    : 0
% 6.71/2.31  #Define  : 0
% 6.71/2.31  #Split   : 5
% 6.71/2.31  #Chain   : 0
% 6.71/2.31  #Close   : 0
% 6.71/2.31  
% 6.71/2.31  Ordering : KBO
% 6.71/2.31  
% 6.71/2.31  Simplification rules
% 6.71/2.31  ----------------------
% 6.71/2.31  #Subsume      : 395
% 6.71/2.31  #Demod        : 2131
% 6.71/2.31  #Tautology    : 420
% 6.71/2.31  #SimpNegUnit  : 3
% 6.71/2.31  #BackRed      : 5
% 6.71/2.31  
% 6.71/2.31  #Partial instantiations: 0
% 6.71/2.31  #Strategies tried      : 1
% 6.71/2.31  
% 6.71/2.31  Timing (in seconds)
% 6.71/2.31  ----------------------
% 6.71/2.32  Preprocessing        : 0.39
% 6.71/2.32  Parsing              : 0.19
% 6.71/2.32  CNF conversion       : 0.05
% 6.71/2.32  Main loop            : 1.08
% 6.71/2.32  Inferencing          : 0.33
% 6.71/2.32  Reduction            : 0.38
% 6.71/2.32  Demodulation         : 0.28
% 6.71/2.32  BG Simplification    : 0.04
% 6.71/2.32  Subsumption          : 0.27
% 6.71/2.32  Abstraction          : 0.05
% 6.71/2.32  MUC search           : 0.00
% 6.71/2.32  Cooper               : 0.00
% 6.71/2.32  Total                : 1.52
% 6.71/2.32  Index Insertion      : 0.00
% 6.71/2.32  Index Deletion       : 0.00
% 6.71/2.32  Index Matching       : 0.00
% 6.71/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
