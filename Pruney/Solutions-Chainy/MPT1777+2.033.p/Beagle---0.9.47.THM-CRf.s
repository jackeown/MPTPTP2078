%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:37 EST 2020

% Result     : Theorem 53.28s
% Output     : CNFRefutation 53.41s
% Verified   : 
% Statistics : Number of formulae       :  207 (3940 expanded)
%              Number of leaves         :   50 (1346 expanded)
%              Depth                    :   25
%              Number of atoms          :  608 (17838 expanded)
%              Number of equality atoms :   49 (2097 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_322,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_198,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_205,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_219,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_194,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_187,axiom,(
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

tff(f_261,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(c_64,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_96,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_82,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_138,plain,(
    ! [B_292,A_293] :
      ( l1_pre_topc(B_292)
      | ~ m1_pre_topc(B_292,A_293)
      | ~ l1_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_138])).

tff(c_151,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_144])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_111,plain,(
    ! [A_290] :
      ( u1_struct_0(A_290) = k2_struct_0(A_290)
      | ~ l1_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_115,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_158,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_151,c_115])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_164,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_72])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_90,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_120,plain,(
    ! [A_291] :
      ( u1_struct_0(A_291) = k2_struct_0(A_291)
      | ~ l1_pre_topc(A_291) ) ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_128,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_90,c_120])).

tff(c_78,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_133,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_78])).

tff(c_163,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_133])).

tff(c_50,plain,(
    ! [A_86] :
      ( m1_pre_topc(A_86,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_86,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_147,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_138])).

tff(c_154,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_147])).

tff(c_162,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_154,c_115])).

tff(c_74,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_170,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_74])).

tff(c_371,plain,(
    ! [B_311,A_312] :
      ( m1_pre_topc(B_311,A_312)
      | ~ m1_pre_topc(B_311,g1_pre_topc(u1_struct_0(A_312),u1_pre_topc(A_312)))
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_374,plain,(
    ! [B_311] :
      ( m1_pre_topc(B_311,'#skF_3')
      | ~ m1_pre_topc(B_311,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_371])).

tff(c_389,plain,(
    ! [B_311] :
      ( m1_pre_topc(B_311,'#skF_3')
      | ~ m1_pre_topc(B_311,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_170,c_374])).

tff(c_218,plain,(
    ! [B_303,A_304] :
      ( r1_tarski(u1_struct_0(B_303),u1_struct_0(A_304))
      | ~ m1_pre_topc(B_303,A_304)
      | ~ l1_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_226,plain,(
    ! [B_303] :
      ( r1_tarski(u1_struct_0(B_303),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_303,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_218])).

tff(c_291,plain,(
    ! [B_307] :
      ( r1_tarski(u1_struct_0(B_307),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_307,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_226])).

tff(c_299,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_291])).

tff(c_431,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_448,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_389,c_431])).

tff(c_451,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_448])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_451])).

tff(c_457,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_456,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_232,plain,(
    ! [B_303] :
      ( r1_tarski(u1_struct_0(B_303),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_303,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_218])).

tff(c_336,plain,(
    ! [B_309] :
      ( r1_tarski(u1_struct_0(B_309),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_309,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_232])).

tff(c_341,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_336])).

tff(c_479,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_556,plain,(
    ! [A_325,B_326] :
      ( m1_pre_topc(A_325,g1_pre_topc(u1_struct_0(B_326),u1_pre_topc(B_326)))
      | ~ m1_pre_topc(A_325,B_326)
      | ~ l1_pre_topc(B_326)
      | ~ l1_pre_topc(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_574,plain,(
    ! [A_325] :
      ( m1_pre_topc(A_325,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_325,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_325) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_556])).

tff(c_604,plain,(
    ! [A_327] :
      ( m1_pre_topc(A_327,'#skF_4')
      | ~ m1_pre_topc(A_327,'#skF_3')
      | ~ l1_pre_topc(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_170,c_574])).

tff(c_614,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_604])).

tff(c_621,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_614])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_621])).

tff(c_624,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_650,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_624,c_2])).

tff(c_653,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_650])).

tff(c_658,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_170])).

tff(c_660,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_162])).

tff(c_809,plain,(
    ! [A_335,B_336] :
      ( m1_pre_topc(A_335,g1_pre_topc(u1_struct_0(B_336),u1_pre_topc(B_336)))
      | ~ m1_pre_topc(A_335,B_336)
      | ~ l1_pre_topc(B_336)
      | ~ l1_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_827,plain,(
    ! [A_335] :
      ( m1_pre_topc(A_335,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_335,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_809])).

tff(c_858,plain,(
    ! [A_337] :
      ( m1_pre_topc(A_337,'#skF_4')
      | ~ m1_pre_topc(A_337,'#skF_3')
      | ~ l1_pre_topc(A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_658,c_827])).

tff(c_861,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_457,c_858])).

tff(c_871,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_861])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_169,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_128,c_76])).

tff(c_180,plain,(
    ! [A_294,B_295] :
      ( r1_tarski(A_294,B_295)
      | ~ m1_subset_1(A_294,k1_zfmisc_1(B_295)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_169,c_180])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_92,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_98,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_201,plain,(
    ! [B_301,A_302] :
      ( v2_pre_topc(B_301)
      | ~ m1_pre_topc(B_301,A_302)
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_207,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_201])).

tff(c_214,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_207])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2863,plain,(
    ! [A_422,B_423,C_424,D_425] :
      ( k2_partfun1(u1_struct_0(A_422),u1_struct_0(B_423),C_424,u1_struct_0(D_425)) = k2_tmap_1(A_422,B_423,C_424,D_425)
      | ~ m1_pre_topc(D_425,A_422)
      | ~ m1_subset_1(C_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_422),u1_struct_0(B_423))))
      | ~ v1_funct_2(C_424,u1_struct_0(A_422),u1_struct_0(B_423))
      | ~ v1_funct_1(C_424)
      | ~ l1_pre_topc(B_423)
      | ~ v2_pre_topc(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5417,plain,(
    ! [A_551,B_552,A_553,D_554] :
      ( k2_partfun1(u1_struct_0(A_551),u1_struct_0(B_552),A_553,u1_struct_0(D_554)) = k2_tmap_1(A_551,B_552,A_553,D_554)
      | ~ m1_pre_topc(D_554,A_551)
      | ~ v1_funct_2(A_553,u1_struct_0(A_551),u1_struct_0(B_552))
      | ~ v1_funct_1(A_553)
      | ~ l1_pre_topc(B_552)
      | ~ v2_pre_topc(B_552)
      | v2_struct_0(B_552)
      | ~ l1_pre_topc(A_551)
      | ~ v2_pre_topc(A_551)
      | v2_struct_0(A_551)
      | ~ r1_tarski(A_553,k2_zfmisc_1(u1_struct_0(A_551),u1_struct_0(B_552))) ) ),
    inference(resolution,[status(thm)],[c_10,c_2863])).

tff(c_5423,plain,(
    ! [B_552,A_553,D_554] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_552),A_553,u1_struct_0(D_554)) = k2_tmap_1('#skF_4',B_552,A_553,D_554)
      | ~ m1_pre_topc(D_554,'#skF_4')
      | ~ v1_funct_2(A_553,u1_struct_0('#skF_4'),u1_struct_0(B_552))
      | ~ v1_funct_1(A_553)
      | ~ l1_pre_topc(B_552)
      | ~ v2_pre_topc(B_552)
      | v2_struct_0(B_552)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_553,k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_552))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_5417])).

tff(c_5444,plain,(
    ! [B_552,A_553,D_554] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_552),A_553,u1_struct_0(D_554)) = k2_tmap_1('#skF_4',B_552,A_553,D_554)
      | ~ m1_pre_topc(D_554,'#skF_4')
      | ~ v1_funct_2(A_553,k2_struct_0('#skF_4'),u1_struct_0(B_552))
      | ~ v1_funct_1(A_553)
      | ~ l1_pre_topc(B_552)
      | ~ v2_pre_topc(B_552)
      | v2_struct_0(B_552)
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_553,k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_552))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_151,c_158,c_158,c_5423])).

tff(c_6060,plain,(
    ! [B_582,A_583,D_584] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_582),A_583,u1_struct_0(D_584)) = k2_tmap_1('#skF_4',B_582,A_583,D_584)
      | ~ m1_pre_topc(D_584,'#skF_4')
      | ~ v1_funct_2(A_583,k2_struct_0('#skF_4'),u1_struct_0(B_582))
      | ~ v1_funct_1(A_583)
      | ~ l1_pre_topc(B_582)
      | ~ v2_pre_topc(B_582)
      | v2_struct_0(B_582)
      | ~ r1_tarski(A_583,k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_582))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5444])).

tff(c_6066,plain,(
    ! [A_583,D_584] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),A_583,u1_struct_0(D_584)) = k2_tmap_1('#skF_4','#skF_2',A_583,D_584)
      | ~ m1_pre_topc(D_584,'#skF_4')
      | ~ v1_funct_2(A_583,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_583)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_583,k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_6060])).

tff(c_6079,plain,(
    ! [A_583,D_584] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),A_583,u1_struct_0(D_584)) = k2_tmap_1('#skF_4','#skF_2',A_583,D_584)
      | ~ m1_pre_topc(D_584,'#skF_4')
      | ~ v1_funct_2(A_583,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_583)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_583,k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_128,c_128,c_6066])).

tff(c_6381,plain,(
    ! [A_598,D_599] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),A_598,u1_struct_0(D_599)) = k2_tmap_1('#skF_4','#skF_2',A_598,D_599)
      | ~ m1_pre_topc(D_599,'#skF_4')
      | ~ v1_funct_2(A_598,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_598)
      | ~ r1_tarski(A_598,k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_6079])).

tff(c_6383,plain,(
    ! [D_599] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_599)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_599)
      | ~ m1_pre_topc(D_599,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_184,c_6381])).

tff(c_6391,plain,(
    ! [D_600] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_600)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_600)
      | ~ m1_pre_topc(D_600,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_163,c_6383])).

tff(c_6403,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_6391])).

tff(c_6415,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_6403])).

tff(c_625,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_100,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_3028,plain,(
    ! [E_435,D_434,A_436,B_437,C_438] :
      ( k3_tmap_1(A_436,B_437,C_438,D_434,E_435) = k2_partfun1(u1_struct_0(C_438),u1_struct_0(B_437),E_435,u1_struct_0(D_434))
      | ~ m1_pre_topc(D_434,C_438)
      | ~ m1_subset_1(E_435,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_438),u1_struct_0(B_437))))
      | ~ v1_funct_2(E_435,u1_struct_0(C_438),u1_struct_0(B_437))
      | ~ v1_funct_1(E_435)
      | ~ m1_pre_topc(D_434,A_436)
      | ~ m1_pre_topc(C_438,A_436)
      | ~ l1_pre_topc(B_437)
      | ~ v2_pre_topc(B_437)
      | v2_struct_0(B_437)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_5811,plain,(
    ! [A_573,C_575,D_574,B_572,A_576] :
      ( k3_tmap_1(A_576,B_572,C_575,D_574,A_573) = k2_partfun1(u1_struct_0(C_575),u1_struct_0(B_572),A_573,u1_struct_0(D_574))
      | ~ m1_pre_topc(D_574,C_575)
      | ~ v1_funct_2(A_573,u1_struct_0(C_575),u1_struct_0(B_572))
      | ~ v1_funct_1(A_573)
      | ~ m1_pre_topc(D_574,A_576)
      | ~ m1_pre_topc(C_575,A_576)
      | ~ l1_pre_topc(B_572)
      | ~ v2_pre_topc(B_572)
      | v2_struct_0(B_572)
      | ~ l1_pre_topc(A_576)
      | ~ v2_pre_topc(A_576)
      | v2_struct_0(A_576)
      | ~ r1_tarski(A_573,k2_zfmisc_1(u1_struct_0(C_575),u1_struct_0(B_572))) ) ),
    inference(resolution,[status(thm)],[c_10,c_3028])).

tff(c_5847,plain,(
    ! [C_575,B_572,A_573] :
      ( k2_partfun1(u1_struct_0(C_575),u1_struct_0(B_572),A_573,u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1',B_572,C_575,'#skF_3',A_573)
      | ~ m1_pre_topc('#skF_3',C_575)
      | ~ v1_funct_2(A_573,u1_struct_0(C_575),u1_struct_0(B_572))
      | ~ v1_funct_1(A_573)
      | ~ m1_pre_topc(C_575,'#skF_1')
      | ~ l1_pre_topc(B_572)
      | ~ v2_pre_topc(B_572)
      | v2_struct_0(B_572)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_573,k2_zfmisc_1(u1_struct_0(C_575),u1_struct_0(B_572))) ) ),
    inference(resolution,[status(thm)],[c_86,c_5811])).

tff(c_5896,plain,(
    ! [C_575,B_572,A_573] :
      ( k2_partfun1(u1_struct_0(C_575),u1_struct_0(B_572),A_573,k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1',B_572,C_575,'#skF_3',A_573)
      | ~ m1_pre_topc('#skF_3',C_575)
      | ~ v1_funct_2(A_573,u1_struct_0(C_575),u1_struct_0(B_572))
      | ~ v1_funct_1(A_573)
      | ~ m1_pre_topc(C_575,'#skF_1')
      | ~ l1_pre_topc(B_572)
      | ~ v2_pre_topc(B_572)
      | v2_struct_0(B_572)
      | v2_struct_0('#skF_1')
      | ~ r1_tarski(A_573,k2_zfmisc_1(u1_struct_0(C_575),u1_struct_0(B_572))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_660,c_5847])).

tff(c_115319,plain,(
    ! [C_2263,B_2264,A_2265] :
      ( k2_partfun1(u1_struct_0(C_2263),u1_struct_0(B_2264),A_2265,k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1',B_2264,C_2263,'#skF_3',A_2265)
      | ~ m1_pre_topc('#skF_3',C_2263)
      | ~ v1_funct_2(A_2265,u1_struct_0(C_2263),u1_struct_0(B_2264))
      | ~ v1_funct_1(A_2265)
      | ~ m1_pre_topc(C_2263,'#skF_1')
      | ~ l1_pre_topc(B_2264)
      | ~ v2_pre_topc(B_2264)
      | v2_struct_0(B_2264)
      | ~ r1_tarski(A_2265,k2_zfmisc_1(u1_struct_0(C_2263),u1_struct_0(B_2264))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_5896])).

tff(c_115337,plain,(
    ! [C_2263,A_2265] :
      ( k2_partfun1(u1_struct_0(C_2263),u1_struct_0('#skF_2'),A_2265,k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2',C_2263,'#skF_3',A_2265)
      | ~ m1_pre_topc('#skF_3',C_2263)
      | ~ v1_funct_2(A_2265,u1_struct_0(C_2263),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(A_2265)
      | ~ m1_pre_topc(C_2263,'#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_2265,k2_zfmisc_1(u1_struct_0(C_2263),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_115319])).

tff(c_115360,plain,(
    ! [C_2263,A_2265] :
      ( k2_partfun1(u1_struct_0(C_2263),k2_struct_0('#skF_2'),A_2265,k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2',C_2263,'#skF_3',A_2265)
      | ~ m1_pre_topc('#skF_3',C_2263)
      | ~ v1_funct_2(A_2265,u1_struct_0(C_2263),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_2265)
      | ~ m1_pre_topc(C_2263,'#skF_1')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_2265,k2_zfmisc_1(u1_struct_0(C_2263),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_128,c_128,c_115337])).

tff(c_115842,plain,(
    ! [C_2281,A_2282] :
      ( k2_partfun1(u1_struct_0(C_2281),k2_struct_0('#skF_2'),A_2282,k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2',C_2281,'#skF_3',A_2282)
      | ~ m1_pre_topc('#skF_3',C_2281)
      | ~ v1_funct_2(A_2282,u1_struct_0(C_2281),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_2282)
      | ~ m1_pre_topc(C_2281,'#skF_1')
      | ~ r1_tarski(A_2282,k2_zfmisc_1(u1_struct_0(C_2281),k2_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_115360])).

tff(c_115848,plain,(
    ! [A_2282] :
      ( k2_partfun1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2'),A_2282,k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',A_2282)
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ v1_funct_2(A_2282,u1_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_2282)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ r1_tarski(A_2282,k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_115842])).

tff(c_115867,plain,(
    ! [A_2283] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),A_2283,k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3',A_2283)
      | ~ v1_funct_2(A_2283,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(A_2283)
      | ~ r1_tarski(A_2283,k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_158,c_625,c_158,c_115848])).

tff(c_115870,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_115867])).

tff(c_115877,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_163,c_6415,c_115870])).

tff(c_68,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_66,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_102,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66])).

tff(c_115879,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115877,c_102])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_322])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1102,plain,(
    ! [B_346,C_347,A_348] :
      ( m1_pre_topc(B_346,C_347)
      | ~ r1_tarski(u1_struct_0(B_346),u1_struct_0(C_347))
      | ~ m1_pre_topc(C_347,A_348)
      | ~ m1_pre_topc(B_346,A_348)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1159,plain,(
    ! [B_352,A_353] :
      ( m1_pre_topc(B_352,B_352)
      | ~ m1_pre_topc(B_352,A_353)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353) ) ),
    inference(resolution,[status(thm)],[c_6,c_1102])).

tff(c_1181,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_1159])).

tff(c_1208,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_1181])).

tff(c_210,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_201])).

tff(c_217,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_210])).

tff(c_36,plain,(
    ! [A_29] :
      ( v3_pre_topc(k2_struct_0(A_29),A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_668,plain,
    ( v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_36])).

tff(c_672,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_154,c_668])).

tff(c_254,plain,(
    ! [B_305,A_306] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ m1_pre_topc(B_305,A_306)
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_269,plain,(
    ! [B_305] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_305,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_254])).

tff(c_947,plain,(
    ! [B_339] :
      ( m1_subset_1(u1_struct_0(B_339),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_339,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_269])).

tff(c_953,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_947])).

tff(c_965,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_953])).

tff(c_1441,plain,(
    ! [B_365,A_366] :
      ( v3_pre_topc(B_365,g1_pre_topc(u1_struct_0(A_366),u1_pre_topc(A_366)))
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ v3_pre_topc(B_365,A_366)
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1444,plain,(
    ! [B_365] :
      ( v3_pre_topc(B_365,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_365,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_1441])).

tff(c_1801,plain,(
    ! [B_379] :
      ( v3_pre_topc(B_379,'#skF_4')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_379,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_154,c_660,c_658,c_1444])).

tff(c_1807,plain,
    ( v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_965,c_1801])).

tff(c_1818,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_1807])).

tff(c_263,plain,(
    ! [B_305] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_305,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_254])).

tff(c_284,plain,(
    ! [B_305] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_305,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_263])).

tff(c_974,plain,(
    ! [B_305] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_305,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_284])).

tff(c_2454,plain,(
    ! [B_406,A_407] :
      ( v3_pre_topc(B_406,A_407)
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_407),u1_pre_topc(A_407)))))
      | ~ v3_pre_topc(B_406,g1_pre_topc(u1_struct_0(A_407),u1_pre_topc(A_407)))
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2476,plain,(
    ! [B_406] :
      ( v3_pre_topc(B_406,'#skF_3')
      | ~ m1_subset_1(B_406,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))))
      | ~ v3_pre_topc(B_406,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_2454])).

tff(c_2509,plain,(
    ! [B_408] :
      ( v3_pre_topc(B_408,'#skF_3')
      | ~ m1_subset_1(B_408,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_408,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_154,c_658,c_660,c_158,c_658,c_2476])).

tff(c_2523,plain,(
    ! [B_305] :
      ( v3_pre_topc(u1_struct_0(B_305),'#skF_3')
      | ~ v3_pre_topc(u1_struct_0(B_305),'#skF_4')
      | ~ m1_pre_topc(B_305,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_974,c_2509])).

tff(c_48,plain,(
    ! [B_85,A_83] :
      ( m1_subset_1(u1_struct_0(B_85),k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ m1_pre_topc(B_85,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1706,plain,(
    ! [B_375,A_376] :
      ( v1_tsep_1(B_375,A_376)
      | ~ v3_pre_topc(u1_struct_0(B_375),A_376)
      | ~ m1_subset_1(u1_struct_0(B_375),k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ m1_pre_topc(B_375,A_376)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_2981,plain,(
    ! [B_431,A_432] :
      ( v1_tsep_1(B_431,A_432)
      | ~ v3_pre_topc(u1_struct_0(B_431),A_432)
      | ~ v2_pre_topc(A_432)
      | ~ m1_pre_topc(B_431,A_432)
      | ~ l1_pre_topc(A_432) ) ),
    inference(resolution,[status(thm)],[c_48,c_1706])).

tff(c_2987,plain,(
    ! [B_305] :
      ( v1_tsep_1(B_305,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_pre_topc(u1_struct_0(B_305),'#skF_4')
      | ~ m1_pre_topc(B_305,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2523,c_2981])).

tff(c_3011,plain,(
    ! [B_433] :
      ( v1_tsep_1(B_433,'#skF_3')
      | ~ v3_pre_topc(u1_struct_0(B_433),'#skF_4')
      | ~ m1_pre_topc(B_433,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_217,c_2987])).

tff(c_3014,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_3011])).

tff(c_3025,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_1818,c_3014])).

tff(c_1938,plain,(
    ! [B_385,A_386] :
      ( v3_pre_topc(u1_struct_0(B_385),A_386)
      | ~ v1_tsep_1(B_385,A_386)
      | ~ m1_subset_1(u1_struct_0(B_385),k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_pre_topc(B_385,A_386)
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_3065,plain,(
    ! [B_439,A_440] :
      ( v3_pre_topc(u1_struct_0(B_439),A_440)
      | ~ v1_tsep_1(B_439,A_440)
      | ~ v2_pre_topc(A_440)
      | ~ m1_pre_topc(B_439,A_440)
      | ~ l1_pre_topc(A_440) ) ),
    inference(resolution,[status(thm)],[c_48,c_1938])).

tff(c_1815,plain,(
    ! [B_305] :
      ( v3_pre_topc(u1_struct_0(B_305),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_305),'#skF_3')
      | ~ m1_pre_topc(B_305,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_974,c_1801])).

tff(c_3076,plain,(
    ! [B_439] :
      ( v3_pre_topc(u1_struct_0(B_439),'#skF_4')
      | ~ v1_tsep_1(B_439,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_439,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3065,c_1815])).

tff(c_3103,plain,(
    ! [B_441] :
      ( v3_pre_topc(u1_struct_0(B_441),'#skF_4')
      | ~ v1_tsep_1(B_441,'#skF_3')
      | ~ m1_pre_topc(B_441,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_217,c_3076])).

tff(c_1740,plain,(
    ! [B_85,A_83] :
      ( v1_tsep_1(B_85,A_83)
      | ~ v3_pre_topc(u1_struct_0(B_85),A_83)
      | ~ v2_pre_topc(A_83)
      | ~ m1_pre_topc(B_85,A_83)
      | ~ l1_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_48,c_1706])).

tff(c_3109,plain,(
    ! [B_441] :
      ( v1_tsep_1(B_441,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_441,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tsep_1(B_441,'#skF_3')
      | ~ m1_pre_topc(B_441,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3103,c_1740])).

tff(c_3136,plain,(
    ! [B_445] :
      ( v1_tsep_1(B_445,'#skF_4')
      | ~ m1_pre_topc(B_445,'#skF_4')
      | ~ v1_tsep_1(B_445,'#skF_3')
      | ~ m1_pre_topc(B_445,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_214,c_3109])).

tff(c_3145,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3025,c_3136])).

tff(c_3152,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1208,c_625,c_3145])).

tff(c_6400,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_6391])).

tff(c_6413,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_6400])).

tff(c_6420,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6415,c_6413])).

tff(c_58,plain,(
    ! [B_129,F_159,D_153,C_145,A_97] :
      ( r1_tmap_1(B_129,A_97,C_145,F_159)
      | ~ r1_tmap_1(D_153,A_97,k2_tmap_1(B_129,A_97,C_145,D_153),F_159)
      | ~ m1_subset_1(F_159,u1_struct_0(D_153))
      | ~ m1_subset_1(F_159,u1_struct_0(B_129))
      | ~ m1_pre_topc(D_153,B_129)
      | ~ v1_tsep_1(D_153,B_129)
      | v2_struct_0(D_153)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_129),u1_struct_0(A_97))))
      | ~ v1_funct_2(C_145,u1_struct_0(B_129),u1_struct_0(A_97))
      | ~ v1_funct_1(C_145)
      | ~ l1_pre_topc(B_129)
      | ~ v2_pre_topc(B_129)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_6427,plain,(
    ! [F_159] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_159)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_159)
      | ~ m1_subset_1(F_159,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_159,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ v1_tsep_1('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6420,c_58])).

tff(c_6431,plain,(
    ! [F_159] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_159)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_159)
      | ~ m1_subset_1(F_159,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_214,c_151,c_80,c_163,c_128,c_158,c_169,c_128,c_158,c_3152,c_625,c_158,c_660,c_6427])).

tff(c_6432,plain,(
    ! [F_159] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_159)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_159)
      | ~ m1_subset_1(F_159,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_84,c_88,c_6431])).

tff(c_116268,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_115879,c_6432])).

tff(c_116274,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_116268])).

tff(c_116276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_116274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:30:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 53.28/42.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.37/42.51  
% 53.37/42.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.37/42.51  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 53.37/42.51  
% 53.37/42.51  %Foreground sorts:
% 53.37/42.51  
% 53.37/42.51  
% 53.37/42.51  %Background operators:
% 53.37/42.51  
% 53.37/42.51  
% 53.37/42.51  %Foreground operators:
% 53.37/42.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 53.37/42.51  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 53.37/42.51  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 53.37/42.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 53.37/42.51  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 53.37/42.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 53.37/42.51  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 53.37/42.51  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 53.37/42.51  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 53.37/42.51  tff('#skF_7', type, '#skF_7': $i).
% 53.37/42.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 53.37/42.51  tff('#skF_5', type, '#skF_5': $i).
% 53.37/42.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 53.37/42.51  tff('#skF_6', type, '#skF_6': $i).
% 53.37/42.51  tff('#skF_2', type, '#skF_2': $i).
% 53.37/42.51  tff('#skF_3', type, '#skF_3': $i).
% 53.37/42.51  tff('#skF_1', type, '#skF_1': $i).
% 53.37/42.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 53.37/42.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 53.37/42.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 53.37/42.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 53.37/42.51  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 53.37/42.51  tff('#skF_4', type, '#skF_4': $i).
% 53.37/42.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 53.37/42.51  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 53.37/42.51  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 53.37/42.51  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 53.37/42.51  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 53.37/42.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 53.37/42.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 53.37/42.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 53.37/42.51  
% 53.41/42.55  tff(f_322, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 53.41/42.55  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 53.41/42.55  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 53.41/42.55  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 53.41/42.55  tff(f_198, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 53.41/42.55  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 53.41/42.55  tff(f_205, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 53.41/42.55  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 53.41/42.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 53.41/42.55  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 53.41/42.55  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 53.41/42.55  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 53.41/42.55  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 53.41/42.55  tff(f_219, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 53.41/42.55  tff(f_110, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 53.41/42.55  tff(f_194, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 53.41/42.55  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_pre_topc)).
% 53.41/42.55  tff(f_187, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 53.41/42.55  tff(f_261, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 53.41/42.55  tff(c_64, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_96, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_82, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_138, plain, (![B_292, A_293]: (l1_pre_topc(B_292) | ~m1_pre_topc(B_292, A_293) | ~l1_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_59])).
% 53.41/42.55  tff(c_144, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_82, c_138])).
% 53.41/42.55  tff(c_151, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_144])).
% 53.41/42.55  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 53.41/42.55  tff(c_111, plain, (![A_290]: (u1_struct_0(A_290)=k2_struct_0(A_290) | ~l1_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_48])).
% 53.41/42.55  tff(c_115, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_16, c_111])).
% 53.41/42.55  tff(c_158, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_151, c_115])).
% 53.41/42.55  tff(c_72, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_164, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_72])).
% 53.41/42.55  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_90, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_120, plain, (![A_291]: (u1_struct_0(A_291)=k2_struct_0(A_291) | ~l1_pre_topc(A_291))), inference(resolution, [status(thm)], [c_16, c_111])).
% 53.41/42.55  tff(c_128, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_90, c_120])).
% 53.41/42.55  tff(c_78, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_133, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_78])).
% 53.41/42.55  tff(c_163, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_133])).
% 53.41/42.55  tff(c_50, plain, (![A_86]: (m1_pre_topc(A_86, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_198])).
% 53.41/42.55  tff(c_86, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_147, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86, c_138])).
% 53.41/42.55  tff(c_154, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_147])).
% 53.41/42.55  tff(c_162, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_154, c_115])).
% 53.41/42.55  tff(c_74, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_170, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_74])).
% 53.41/42.55  tff(c_371, plain, (![B_311, A_312]: (m1_pre_topc(B_311, A_312) | ~m1_pre_topc(B_311, g1_pre_topc(u1_struct_0(A_312), u1_pre_topc(A_312))) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_82])).
% 53.41/42.55  tff(c_374, plain, (![B_311]: (m1_pre_topc(B_311, '#skF_3') | ~m1_pre_topc(B_311, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_371])).
% 53.41/42.55  tff(c_389, plain, (![B_311]: (m1_pre_topc(B_311, '#skF_3') | ~m1_pre_topc(B_311, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_170, c_374])).
% 53.41/42.55  tff(c_218, plain, (![B_303, A_304]: (r1_tarski(u1_struct_0(B_303), u1_struct_0(A_304)) | ~m1_pre_topc(B_303, A_304) | ~l1_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_205])).
% 53.41/42.55  tff(c_226, plain, (![B_303]: (r1_tarski(u1_struct_0(B_303), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_303, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_218])).
% 53.41/42.55  tff(c_291, plain, (![B_307]: (r1_tarski(u1_struct_0(B_307), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_307, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_226])).
% 53.41/42.55  tff(c_299, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_158, c_291])).
% 53.41/42.55  tff(c_431, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_299])).
% 53.41/42.55  tff(c_448, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_389, c_431])).
% 53.41/42.55  tff(c_451, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_448])).
% 53.41/42.55  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_451])).
% 53.41/42.55  tff(c_457, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_299])).
% 53.41/42.55  tff(c_456, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_299])).
% 53.41/42.55  tff(c_232, plain, (![B_303]: (r1_tarski(u1_struct_0(B_303), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_303, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_218])).
% 53.41/42.55  tff(c_336, plain, (![B_309]: (r1_tarski(u1_struct_0(B_309), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_309, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_232])).
% 53.41/42.55  tff(c_341, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_336])).
% 53.41/42.55  tff(c_479, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_341])).
% 53.41/42.55  tff(c_556, plain, (![A_325, B_326]: (m1_pre_topc(A_325, g1_pre_topc(u1_struct_0(B_326), u1_pre_topc(B_326))) | ~m1_pre_topc(A_325, B_326) | ~l1_pre_topc(B_326) | ~l1_pre_topc(A_325))), inference(cnfTransformation, [status(thm)], [f_104])).
% 53.41/42.55  tff(c_574, plain, (![A_325]: (m1_pre_topc(A_325, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_325, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_325))), inference(superposition, [status(thm), theory('equality')], [c_162, c_556])).
% 53.41/42.55  tff(c_604, plain, (![A_327]: (m1_pre_topc(A_327, '#skF_4') | ~m1_pre_topc(A_327, '#skF_3') | ~l1_pre_topc(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_170, c_574])).
% 53.41/42.55  tff(c_614, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_604])).
% 53.41/42.55  tff(c_621, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_614])).
% 53.41/42.55  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_479, c_621])).
% 53.41/42.55  tff(c_624, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_341])).
% 53.41/42.55  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 53.41/42.55  tff(c_650, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_624, c_2])).
% 53.41/42.55  tff(c_653, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_650])).
% 53.41/42.55  tff(c_658, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_653, c_170])).
% 53.41/42.55  tff(c_660, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_162])).
% 53.41/42.55  tff(c_809, plain, (![A_335, B_336]: (m1_pre_topc(A_335, g1_pre_topc(u1_struct_0(B_336), u1_pre_topc(B_336))) | ~m1_pre_topc(A_335, B_336) | ~l1_pre_topc(B_336) | ~l1_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_104])).
% 53.41/42.55  tff(c_827, plain, (![A_335]: (m1_pre_topc(A_335, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_335, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_335))), inference(superposition, [status(thm), theory('equality')], [c_660, c_809])).
% 53.41/42.55  tff(c_858, plain, (![A_337]: (m1_pre_topc(A_337, '#skF_4') | ~m1_pre_topc(A_337, '#skF_3') | ~l1_pre_topc(A_337))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_658, c_827])).
% 53.41/42.55  tff(c_861, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_457, c_858])).
% 53.41/42.55  tff(c_871, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_861])).
% 53.41/42.55  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_169, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_128, c_76])).
% 53.41/42.55  tff(c_180, plain, (![A_294, B_295]: (r1_tarski(A_294, B_295) | ~m1_subset_1(A_294, k1_zfmisc_1(B_295)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 53.41/42.55  tff(c_184, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_169, c_180])).
% 53.41/42.55  tff(c_94, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_92, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_84, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_98, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_201, plain, (![B_301, A_302]: (v2_pre_topc(B_301) | ~m1_pre_topc(B_301, A_302) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_44])).
% 53.41/42.55  tff(c_207, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_82, c_201])).
% 53.41/42.55  tff(c_214, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_207])).
% 53.41/42.55  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 53.41/42.55  tff(c_2863, plain, (![A_422, B_423, C_424, D_425]: (k2_partfun1(u1_struct_0(A_422), u1_struct_0(B_423), C_424, u1_struct_0(D_425))=k2_tmap_1(A_422, B_423, C_424, D_425) | ~m1_pre_topc(D_425, A_422) | ~m1_subset_1(C_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_422), u1_struct_0(B_423)))) | ~v1_funct_2(C_424, u1_struct_0(A_422), u1_struct_0(B_423)) | ~v1_funct_1(C_424) | ~l1_pre_topc(B_423) | ~v2_pre_topc(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_137])).
% 53.41/42.55  tff(c_5417, plain, (![A_551, B_552, A_553, D_554]: (k2_partfun1(u1_struct_0(A_551), u1_struct_0(B_552), A_553, u1_struct_0(D_554))=k2_tmap_1(A_551, B_552, A_553, D_554) | ~m1_pre_topc(D_554, A_551) | ~v1_funct_2(A_553, u1_struct_0(A_551), u1_struct_0(B_552)) | ~v1_funct_1(A_553) | ~l1_pre_topc(B_552) | ~v2_pre_topc(B_552) | v2_struct_0(B_552) | ~l1_pre_topc(A_551) | ~v2_pre_topc(A_551) | v2_struct_0(A_551) | ~r1_tarski(A_553, k2_zfmisc_1(u1_struct_0(A_551), u1_struct_0(B_552))))), inference(resolution, [status(thm)], [c_10, c_2863])).
% 53.41/42.55  tff(c_5423, plain, (![B_552, A_553, D_554]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_552), A_553, u1_struct_0(D_554))=k2_tmap_1('#skF_4', B_552, A_553, D_554) | ~m1_pre_topc(D_554, '#skF_4') | ~v1_funct_2(A_553, u1_struct_0('#skF_4'), u1_struct_0(B_552)) | ~v1_funct_1(A_553) | ~l1_pre_topc(B_552) | ~v2_pre_topc(B_552) | v2_struct_0(B_552) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_553, k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_552))))), inference(superposition, [status(thm), theory('equality')], [c_158, c_5417])).
% 53.41/42.55  tff(c_5444, plain, (![B_552, A_553, D_554]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_552), A_553, u1_struct_0(D_554))=k2_tmap_1('#skF_4', B_552, A_553, D_554) | ~m1_pre_topc(D_554, '#skF_4') | ~v1_funct_2(A_553, k2_struct_0('#skF_4'), u1_struct_0(B_552)) | ~v1_funct_1(A_553) | ~l1_pre_topc(B_552) | ~v2_pre_topc(B_552) | v2_struct_0(B_552) | v2_struct_0('#skF_4') | ~r1_tarski(A_553, k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_552))))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_151, c_158, c_158, c_5423])).
% 53.41/42.55  tff(c_6060, plain, (![B_582, A_583, D_584]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_582), A_583, u1_struct_0(D_584))=k2_tmap_1('#skF_4', B_582, A_583, D_584) | ~m1_pre_topc(D_584, '#skF_4') | ~v1_funct_2(A_583, k2_struct_0('#skF_4'), u1_struct_0(B_582)) | ~v1_funct_1(A_583) | ~l1_pre_topc(B_582) | ~v2_pre_topc(B_582) | v2_struct_0(B_582) | ~r1_tarski(A_583, k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_582))))), inference(negUnitSimplification, [status(thm)], [c_84, c_5444])).
% 53.41/42.55  tff(c_6066, plain, (![A_583, D_584]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), A_583, u1_struct_0(D_584))=k2_tmap_1('#skF_4', '#skF_2', A_583, D_584) | ~m1_pre_topc(D_584, '#skF_4') | ~v1_funct_2(A_583, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(A_583) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_583, k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_128, c_6060])).
% 53.41/42.55  tff(c_6079, plain, (![A_583, D_584]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), A_583, u1_struct_0(D_584))=k2_tmap_1('#skF_4', '#skF_2', A_583, D_584) | ~m1_pre_topc(D_584, '#skF_4') | ~v1_funct_2(A_583, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_583) | v2_struct_0('#skF_2') | ~r1_tarski(A_583, k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_128, c_128, c_6066])).
% 53.41/42.55  tff(c_6381, plain, (![A_598, D_599]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), A_598, u1_struct_0(D_599))=k2_tmap_1('#skF_4', '#skF_2', A_598, D_599) | ~m1_pre_topc(D_599, '#skF_4') | ~v1_funct_2(A_598, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_598) | ~r1_tarski(A_598, k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_94, c_6079])).
% 53.41/42.55  tff(c_6383, plain, (![D_599]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_599))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_599) | ~m1_pre_topc(D_599, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_184, c_6381])).
% 53.41/42.55  tff(c_6391, plain, (![D_600]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_600))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_600) | ~m1_pre_topc(D_600, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_163, c_6383])).
% 53.41/42.55  tff(c_6403, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_158, c_6391])).
% 53.41/42.55  tff(c_6415, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_871, c_6403])).
% 53.41/42.55  tff(c_625, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_341])).
% 53.41/42.55  tff(c_100, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_3028, plain, (![E_435, D_434, A_436, B_437, C_438]: (k3_tmap_1(A_436, B_437, C_438, D_434, E_435)=k2_partfun1(u1_struct_0(C_438), u1_struct_0(B_437), E_435, u1_struct_0(D_434)) | ~m1_pre_topc(D_434, C_438) | ~m1_subset_1(E_435, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_438), u1_struct_0(B_437)))) | ~v1_funct_2(E_435, u1_struct_0(C_438), u1_struct_0(B_437)) | ~v1_funct_1(E_435) | ~m1_pre_topc(D_434, A_436) | ~m1_pre_topc(C_438, A_436) | ~l1_pre_topc(B_437) | ~v2_pre_topc(B_437) | v2_struct_0(B_437) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_169])).
% 53.41/42.55  tff(c_5811, plain, (![A_573, C_575, D_574, B_572, A_576]: (k3_tmap_1(A_576, B_572, C_575, D_574, A_573)=k2_partfun1(u1_struct_0(C_575), u1_struct_0(B_572), A_573, u1_struct_0(D_574)) | ~m1_pre_topc(D_574, C_575) | ~v1_funct_2(A_573, u1_struct_0(C_575), u1_struct_0(B_572)) | ~v1_funct_1(A_573) | ~m1_pre_topc(D_574, A_576) | ~m1_pre_topc(C_575, A_576) | ~l1_pre_topc(B_572) | ~v2_pre_topc(B_572) | v2_struct_0(B_572) | ~l1_pre_topc(A_576) | ~v2_pre_topc(A_576) | v2_struct_0(A_576) | ~r1_tarski(A_573, k2_zfmisc_1(u1_struct_0(C_575), u1_struct_0(B_572))))), inference(resolution, [status(thm)], [c_10, c_3028])).
% 53.41/42.55  tff(c_5847, plain, (![C_575, B_572, A_573]: (k2_partfun1(u1_struct_0(C_575), u1_struct_0(B_572), A_573, u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', B_572, C_575, '#skF_3', A_573) | ~m1_pre_topc('#skF_3', C_575) | ~v1_funct_2(A_573, u1_struct_0(C_575), u1_struct_0(B_572)) | ~v1_funct_1(A_573) | ~m1_pre_topc(C_575, '#skF_1') | ~l1_pre_topc(B_572) | ~v2_pre_topc(B_572) | v2_struct_0(B_572) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tarski(A_573, k2_zfmisc_1(u1_struct_0(C_575), u1_struct_0(B_572))))), inference(resolution, [status(thm)], [c_86, c_5811])).
% 53.41/42.55  tff(c_5896, plain, (![C_575, B_572, A_573]: (k2_partfun1(u1_struct_0(C_575), u1_struct_0(B_572), A_573, k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', B_572, C_575, '#skF_3', A_573) | ~m1_pre_topc('#skF_3', C_575) | ~v1_funct_2(A_573, u1_struct_0(C_575), u1_struct_0(B_572)) | ~v1_funct_1(A_573) | ~m1_pre_topc(C_575, '#skF_1') | ~l1_pre_topc(B_572) | ~v2_pre_topc(B_572) | v2_struct_0(B_572) | v2_struct_0('#skF_1') | ~r1_tarski(A_573, k2_zfmisc_1(u1_struct_0(C_575), u1_struct_0(B_572))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_660, c_5847])).
% 53.41/42.55  tff(c_115319, plain, (![C_2263, B_2264, A_2265]: (k2_partfun1(u1_struct_0(C_2263), u1_struct_0(B_2264), A_2265, k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', B_2264, C_2263, '#skF_3', A_2265) | ~m1_pre_topc('#skF_3', C_2263) | ~v1_funct_2(A_2265, u1_struct_0(C_2263), u1_struct_0(B_2264)) | ~v1_funct_1(A_2265) | ~m1_pre_topc(C_2263, '#skF_1') | ~l1_pre_topc(B_2264) | ~v2_pre_topc(B_2264) | v2_struct_0(B_2264) | ~r1_tarski(A_2265, k2_zfmisc_1(u1_struct_0(C_2263), u1_struct_0(B_2264))))), inference(negUnitSimplification, [status(thm)], [c_100, c_5896])).
% 53.41/42.55  tff(c_115337, plain, (![C_2263, A_2265]: (k2_partfun1(u1_struct_0(C_2263), u1_struct_0('#skF_2'), A_2265, k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', C_2263, '#skF_3', A_2265) | ~m1_pre_topc('#skF_3', C_2263) | ~v1_funct_2(A_2265, u1_struct_0(C_2263), u1_struct_0('#skF_2')) | ~v1_funct_1(A_2265) | ~m1_pre_topc(C_2263, '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_2265, k2_zfmisc_1(u1_struct_0(C_2263), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_128, c_115319])).
% 53.41/42.55  tff(c_115360, plain, (![C_2263, A_2265]: (k2_partfun1(u1_struct_0(C_2263), k2_struct_0('#skF_2'), A_2265, k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', C_2263, '#skF_3', A_2265) | ~m1_pre_topc('#skF_3', C_2263) | ~v1_funct_2(A_2265, u1_struct_0(C_2263), k2_struct_0('#skF_2')) | ~v1_funct_1(A_2265) | ~m1_pre_topc(C_2263, '#skF_1') | v2_struct_0('#skF_2') | ~r1_tarski(A_2265, k2_zfmisc_1(u1_struct_0(C_2263), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_128, c_128, c_115337])).
% 53.41/42.55  tff(c_115842, plain, (![C_2281, A_2282]: (k2_partfun1(u1_struct_0(C_2281), k2_struct_0('#skF_2'), A_2282, k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', C_2281, '#skF_3', A_2282) | ~m1_pre_topc('#skF_3', C_2281) | ~v1_funct_2(A_2282, u1_struct_0(C_2281), k2_struct_0('#skF_2')) | ~v1_funct_1(A_2282) | ~m1_pre_topc(C_2281, '#skF_1') | ~r1_tarski(A_2282, k2_zfmisc_1(u1_struct_0(C_2281), k2_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_94, c_115360])).
% 53.41/42.55  tff(c_115848, plain, (![A_2282]: (k2_partfun1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'), A_2282, k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', A_2282) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_funct_2(A_2282, u1_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_2282) | ~m1_pre_topc('#skF_4', '#skF_1') | ~r1_tarski(A_2282, k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_158, c_115842])).
% 53.41/42.55  tff(c_115867, plain, (![A_2283]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), A_2283, k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', A_2283) | ~v1_funct_2(A_2283, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(A_2283) | ~r1_tarski(A_2283, k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_158, c_625, c_158, c_115848])).
% 53.41/42.55  tff(c_115870, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_184, c_115867])).
% 53.41/42.55  tff(c_115877, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_163, c_6415, c_115870])).
% 53.41/42.55  tff(c_68, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_66, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_102, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66])).
% 53.41/42.55  tff(c_115879, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_115877, c_102])).
% 53.41/42.55  tff(c_88, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_322])).
% 53.41/42.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 53.41/42.55  tff(c_1102, plain, (![B_346, C_347, A_348]: (m1_pre_topc(B_346, C_347) | ~r1_tarski(u1_struct_0(B_346), u1_struct_0(C_347)) | ~m1_pre_topc(C_347, A_348) | ~m1_pre_topc(B_346, A_348) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348))), inference(cnfTransformation, [status(thm)], [f_219])).
% 53.41/42.55  tff(c_1159, plain, (![B_352, A_353]: (m1_pre_topc(B_352, B_352) | ~m1_pre_topc(B_352, A_353) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353))), inference(resolution, [status(thm)], [c_6, c_1102])).
% 53.41/42.55  tff(c_1181, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86, c_1159])).
% 53.41/42.55  tff(c_1208, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_1181])).
% 53.41/42.55  tff(c_210, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_86, c_201])).
% 53.41/42.55  tff(c_217, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_210])).
% 53.41/42.55  tff(c_36, plain, (![A_29]: (v3_pre_topc(k2_struct_0(A_29), A_29) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_110])).
% 53.41/42.55  tff(c_668, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_653, c_36])).
% 53.41/42.55  tff(c_672, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_154, c_668])).
% 53.41/42.55  tff(c_254, plain, (![B_305, A_306]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(u1_struct_0(A_306))) | ~m1_pre_topc(B_305, A_306) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_194])).
% 53.41/42.55  tff(c_269, plain, (![B_305]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_305, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_254])).
% 53.41/42.55  tff(c_947, plain, (![B_339]: (m1_subset_1(u1_struct_0(B_339), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_339, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_269])).
% 53.41/42.55  tff(c_953, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_660, c_947])).
% 53.41/42.55  tff(c_965, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_953])).
% 53.41/42.55  tff(c_1441, plain, (![B_365, A_366]: (v3_pre_topc(B_365, g1_pre_topc(u1_struct_0(A_366), u1_pre_topc(A_366))) | ~m1_subset_1(B_365, k1_zfmisc_1(u1_struct_0(A_366))) | ~v3_pre_topc(B_365, A_366) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366))), inference(cnfTransformation, [status(thm)], [f_95])).
% 53.41/42.55  tff(c_1444, plain, (![B_365]: (v3_pre_topc(B_365, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(B_365, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_365, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_660, c_1441])).
% 53.41/42.55  tff(c_1801, plain, (![B_379]: (v3_pre_topc(B_379, '#skF_4') | ~m1_subset_1(B_379, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v3_pre_topc(B_379, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_154, c_660, c_658, c_1444])).
% 53.41/42.55  tff(c_1807, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_965, c_1801])).
% 53.41/42.55  tff(c_1818, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_672, c_1807])).
% 53.41/42.55  tff(c_263, plain, (![B_305]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_305, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_162, c_254])).
% 53.41/42.55  tff(c_284, plain, (![B_305]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_305, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_263])).
% 53.41/42.55  tff(c_974, plain, (![B_305]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_305, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_284])).
% 53.41/42.55  tff(c_2454, plain, (![B_406, A_407]: (v3_pre_topc(B_406, A_407) | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_407), u1_pre_topc(A_407))))) | ~v3_pre_topc(B_406, g1_pre_topc(u1_struct_0(A_407), u1_pre_topc(A_407))) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407))), inference(cnfTransformation, [status(thm)], [f_95])).
% 53.41/42.55  tff(c_2476, plain, (![B_406]: (v3_pre_topc(B_406, '#skF_3') | ~m1_subset_1(B_406, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))))) | ~v3_pre_topc(B_406, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_660, c_2454])).
% 53.41/42.55  tff(c_2509, plain, (![B_408]: (v3_pre_topc(B_408, '#skF_3') | ~m1_subset_1(B_408, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v3_pre_topc(B_408, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_154, c_658, c_660, c_158, c_658, c_2476])).
% 53.41/42.55  tff(c_2523, plain, (![B_305]: (v3_pre_topc(u1_struct_0(B_305), '#skF_3') | ~v3_pre_topc(u1_struct_0(B_305), '#skF_4') | ~m1_pre_topc(B_305, '#skF_3'))), inference(resolution, [status(thm)], [c_974, c_2509])).
% 53.41/42.55  tff(c_48, plain, (![B_85, A_83]: (m1_subset_1(u1_struct_0(B_85), k1_zfmisc_1(u1_struct_0(A_83))) | ~m1_pre_topc(B_85, A_83) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_194])).
% 53.41/42.55  tff(c_1706, plain, (![B_375, A_376]: (v1_tsep_1(B_375, A_376) | ~v3_pre_topc(u1_struct_0(B_375), A_376) | ~m1_subset_1(u1_struct_0(B_375), k1_zfmisc_1(u1_struct_0(A_376))) | ~m1_pre_topc(B_375, A_376) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376))), inference(cnfTransformation, [status(thm)], [f_187])).
% 53.41/42.55  tff(c_2981, plain, (![B_431, A_432]: (v1_tsep_1(B_431, A_432) | ~v3_pre_topc(u1_struct_0(B_431), A_432) | ~v2_pre_topc(A_432) | ~m1_pre_topc(B_431, A_432) | ~l1_pre_topc(A_432))), inference(resolution, [status(thm)], [c_48, c_1706])).
% 53.41/42.55  tff(c_2987, plain, (![B_305]: (v1_tsep_1(B_305, '#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_pre_topc(u1_struct_0(B_305), '#skF_4') | ~m1_pre_topc(B_305, '#skF_3'))), inference(resolution, [status(thm)], [c_2523, c_2981])).
% 53.41/42.55  tff(c_3011, plain, (![B_433]: (v1_tsep_1(B_433, '#skF_3') | ~v3_pre_topc(u1_struct_0(B_433), '#skF_4') | ~m1_pre_topc(B_433, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_217, c_2987])).
% 53.41/42.55  tff(c_3014, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_660, c_3011])).
% 53.41/42.55  tff(c_3025, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_1818, c_3014])).
% 53.41/42.55  tff(c_1938, plain, (![B_385, A_386]: (v3_pre_topc(u1_struct_0(B_385), A_386) | ~v1_tsep_1(B_385, A_386) | ~m1_subset_1(u1_struct_0(B_385), k1_zfmisc_1(u1_struct_0(A_386))) | ~m1_pre_topc(B_385, A_386) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386))), inference(cnfTransformation, [status(thm)], [f_187])).
% 53.41/42.55  tff(c_3065, plain, (![B_439, A_440]: (v3_pre_topc(u1_struct_0(B_439), A_440) | ~v1_tsep_1(B_439, A_440) | ~v2_pre_topc(A_440) | ~m1_pre_topc(B_439, A_440) | ~l1_pre_topc(A_440))), inference(resolution, [status(thm)], [c_48, c_1938])).
% 53.41/42.55  tff(c_1815, plain, (![B_305]: (v3_pre_topc(u1_struct_0(B_305), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_305), '#skF_3') | ~m1_pre_topc(B_305, '#skF_3'))), inference(resolution, [status(thm)], [c_974, c_1801])).
% 53.41/42.55  tff(c_3076, plain, (![B_439]: (v3_pre_topc(u1_struct_0(B_439), '#skF_4') | ~v1_tsep_1(B_439, '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc(B_439, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_3065, c_1815])).
% 53.41/42.55  tff(c_3103, plain, (![B_441]: (v3_pre_topc(u1_struct_0(B_441), '#skF_4') | ~v1_tsep_1(B_441, '#skF_3') | ~m1_pre_topc(B_441, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_217, c_3076])).
% 53.41/42.55  tff(c_1740, plain, (![B_85, A_83]: (v1_tsep_1(B_85, A_83) | ~v3_pre_topc(u1_struct_0(B_85), A_83) | ~v2_pre_topc(A_83) | ~m1_pre_topc(B_85, A_83) | ~l1_pre_topc(A_83))), inference(resolution, [status(thm)], [c_48, c_1706])).
% 53.41/42.55  tff(c_3109, plain, (![B_441]: (v1_tsep_1(B_441, '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc(B_441, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tsep_1(B_441, '#skF_3') | ~m1_pre_topc(B_441, '#skF_3'))), inference(resolution, [status(thm)], [c_3103, c_1740])).
% 53.41/42.55  tff(c_3136, plain, (![B_445]: (v1_tsep_1(B_445, '#skF_4') | ~m1_pre_topc(B_445, '#skF_4') | ~v1_tsep_1(B_445, '#skF_3') | ~m1_pre_topc(B_445, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_214, c_3109])).
% 53.41/42.55  tff(c_3145, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3025, c_3136])).
% 53.41/42.55  tff(c_3152, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1208, c_625, c_3145])).
% 53.41/42.55  tff(c_6400, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_660, c_6391])).
% 53.41/42.55  tff(c_6413, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_625, c_6400])).
% 53.41/42.55  tff(c_6420, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6415, c_6413])).
% 53.41/42.55  tff(c_58, plain, (![B_129, F_159, D_153, C_145, A_97]: (r1_tmap_1(B_129, A_97, C_145, F_159) | ~r1_tmap_1(D_153, A_97, k2_tmap_1(B_129, A_97, C_145, D_153), F_159) | ~m1_subset_1(F_159, u1_struct_0(D_153)) | ~m1_subset_1(F_159, u1_struct_0(B_129)) | ~m1_pre_topc(D_153, B_129) | ~v1_tsep_1(D_153, B_129) | v2_struct_0(D_153) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_129), u1_struct_0(A_97)))) | ~v1_funct_2(C_145, u1_struct_0(B_129), u1_struct_0(A_97)) | ~v1_funct_1(C_145) | ~l1_pre_topc(B_129) | ~v2_pre_topc(B_129) | v2_struct_0(B_129) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_261])).
% 53.41/42.55  tff(c_6427, plain, (![F_159]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_159) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_159) | ~m1_subset_1(F_159, u1_struct_0('#skF_3')) | ~m1_subset_1(F_159, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6420, c_58])).
% 53.41/42.55  tff(c_6431, plain, (![F_159]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_159) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_159) | ~m1_subset_1(F_159, k2_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_214, c_151, c_80, c_163, c_128, c_158, c_169, c_128, c_158, c_3152, c_625, c_158, c_660, c_6427])).
% 53.41/42.55  tff(c_6432, plain, (![F_159]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_159) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_159) | ~m1_subset_1(F_159, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_94, c_84, c_88, c_6431])).
% 53.41/42.55  tff(c_116268, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_115879, c_6432])).
% 53.41/42.55  tff(c_116274, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_164, c_116268])).
% 53.41/42.55  tff(c_116276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_116274])).
% 53.41/42.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 53.41/42.55  
% 53.41/42.55  Inference rules
% 53.41/42.55  ----------------------
% 53.41/42.55  #Ref     : 0
% 53.41/42.55  #Sup     : 25071
% 53.41/42.55  #Fact    : 0
% 53.41/42.55  #Define  : 0
% 53.41/42.55  #Split   : 83
% 53.41/42.55  #Chain   : 0
% 53.41/42.55  #Close   : 0
% 53.41/42.55  
% 53.41/42.55  Ordering : KBO
% 53.41/42.55  
% 53.41/42.55  Simplification rules
% 53.41/42.55  ----------------------
% 53.41/42.55  #Subsume      : 15090
% 53.41/42.55  #Demod        : 53122
% 53.41/42.55  #Tautology    : 3112
% 53.41/42.55  #SimpNegUnit  : 1521
% 53.41/42.55  #BackRed      : 14
% 53.41/42.55  
% 53.41/42.55  #Partial instantiations: 0
% 53.41/42.55  #Strategies tried      : 1
% 53.41/42.55  
% 53.41/42.55  Timing (in seconds)
% 53.41/42.55  ----------------------
% 53.41/42.55  Preprocessing        : 0.42
% 53.41/42.55  Parsing              : 0.22
% 53.41/42.55  CNF conversion       : 0.05
% 53.41/42.55  Main loop            : 41.32
% 53.41/42.55  Inferencing          : 3.98
% 53.41/42.55  Reduction            : 11.72
% 53.41/42.55  Demodulation         : 9.23
% 53.41/42.55  BG Simplification    : 0.29
% 53.41/42.55  Subsumption          : 24.10
% 53.41/42.55  Abstraction          : 0.92
% 53.41/42.55  MUC search           : 0.00
% 53.41/42.55  Cooper               : 0.00
% 53.41/42.55  Total                : 41.81
% 53.41/42.55  Index Insertion      : 0.00
% 53.41/42.55  Index Deletion       : 0.00
% 53.41/42.55  Index Matching       : 0.00
% 53.41/42.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
