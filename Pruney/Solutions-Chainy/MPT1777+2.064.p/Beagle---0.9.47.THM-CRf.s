%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:41 EST 2020

% Result     : Theorem 5.48s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :  153 (1213 expanded)
%              Number of leaves         :   44 ( 442 expanded)
%              Depth                    :   15
%              Number of atoms          :  346 (5809 expanded)
%              Number of equality atoms :   16 ( 624 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_221,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_99,axiom,(
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

tff(f_172,axiom,(
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

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_127,plain,(
    ! [B_289,A_290] :
      ( l1_pre_topc(B_289)
      | ~ m1_pre_topc(B_289,A_290)
      | ~ l1_pre_topc(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_127])).

tff(c_143,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_136])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_104,plain,(
    ! [A_287] :
      ( u1_struct_0(A_287) = k2_struct_0(A_287)
      | ~ l1_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_108,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_151,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_143,c_108])).

tff(c_109,plain,(
    ! [A_288] :
      ( u1_struct_0(A_288) = k2_struct_0(A_288)
      | ~ l1_pre_topc(A_288) ) ),
    inference(resolution,[status(thm)],[c_10,c_104])).

tff(c_116,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_109])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_118,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_58])).

tff(c_169,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_118])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_158,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_56])).

tff(c_159,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_158])).

tff(c_171,plain,(
    ! [B_292,A_293] :
      ( v2_pre_topc(B_292)
      | ~ m1_pre_topc(B_292,A_293)
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_177,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_171])).

tff(c_184,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_177])).

tff(c_133,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_127])).

tff(c_140,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_133])).

tff(c_36,plain,(
    ! [A_28] :
      ( m1_pre_topc(A_28,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_147,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_108])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_152,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_54])).

tff(c_302,plain,(
    ! [A_304,B_305] :
      ( m1_pre_topc(A_304,B_305)
      | ~ m1_pre_topc(A_304,g1_pre_topc(u1_struct_0(B_305),u1_pre_topc(B_305)))
      | ~ l1_pre_topc(B_305)
      | ~ l1_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_308,plain,(
    ! [A_304] :
      ( m1_pre_topc(A_304,'#skF_3')
      | ~ m1_pre_topc(A_304,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_302])).

tff(c_322,plain,(
    ! [A_304] :
      ( m1_pre_topc(A_304,'#skF_3')
      | ~ m1_pre_topc(A_304,'#skF_4')
      | ~ l1_pre_topc(A_304) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_152,c_308])).

tff(c_188,plain,(
    ! [B_294,A_295] :
      ( m1_subset_1(u1_struct_0(B_294),k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ m1_pre_topc(B_294,A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_200,plain,(
    ! [B_294] :
      ( m1_subset_1(u1_struct_0(B_294),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_294,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_188])).

tff(c_277,plain,(
    ! [B_302] :
      ( m1_subset_1(u1_struct_0(B_302),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_302,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_200])).

tff(c_280,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_277])).

tff(c_401,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_447,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_322,c_401])).

tff(c_450,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_447])).

tff(c_453,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_450])).

tff(c_457,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_453])).

tff(c_459,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_194,plain,(
    ! [B_294] :
      ( m1_subset_1(u1_struct_0(B_294),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_294,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_188])).

tff(c_221,plain,(
    ! [B_296] :
      ( m1_subset_1(u1_struct_0(B_296),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_296,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_194])).

tff(c_227,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_221])).

tff(c_477,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_478,plain,(
    ! [A_311,B_312] :
      ( m1_pre_topc(A_311,g1_pre_topc(u1_struct_0(B_312),u1_pre_topc(B_312)))
      | ~ m1_pre_topc(A_311,B_312)
      | ~ l1_pre_topc(B_312)
      | ~ l1_pre_topc(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_499,plain,(
    ! [A_311] :
      ( m1_pre_topc(A_311,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_311,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_311) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_478])).

tff(c_527,plain,(
    ! [A_313] :
      ( m1_pre_topc(A_313,'#skF_4')
      | ~ m1_pre_topc(A_313,'#skF_3')
      | ~ l1_pre_topc(A_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_152,c_499])).

tff(c_541,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_527])).

tff(c_552,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_541])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_552])).

tff(c_556,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_38,plain,(
    ! [C_35,A_29,B_33] :
      ( m1_pre_topc(C_35,A_29)
      | ~ m1_pre_topc(C_35,B_33)
      | ~ m1_pre_topc(B_33,A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_571,plain,(
    ! [A_29] :
      ( m1_pre_topc('#skF_3',A_29)
      | ~ m1_pre_topc('#skF_4',A_29)
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_556,c_38])).

tff(c_26,plain,(
    ! [A_17] :
      ( v3_pre_topc(k2_struct_0(A_17),A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_975,plain,(
    ! [B_328,A_329] :
      ( v3_pre_topc(B_328,g1_pre_topc(u1_struct_0(A_329),u1_pre_topc(A_329)))
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ v3_pre_topc(B_328,A_329)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_981,plain,(
    ! [B_328] :
      ( v3_pre_topc(B_328,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_328,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_975])).

tff(c_996,plain,(
    ! [B_330] :
      ( v3_pre_topc(B_330,'#skF_4')
      | ~ m1_subset_1(B_330,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_330,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_140,c_147,c_152,c_981])).

tff(c_1009,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_996])).

tff(c_1010,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1009])).

tff(c_1013,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1010])).

tff(c_1017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_140,c_1013])).

tff(c_1019,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1009])).

tff(c_1670,plain,(
    ! [B_353,A_354] :
      ( v1_tsep_1(B_353,A_354)
      | ~ v3_pre_topc(u1_struct_0(B_353),A_354)
      | ~ m1_subset_1(u1_struct_0(B_353),k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ m1_pre_topc(B_353,A_354)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1756,plain,(
    ! [B_357] :
      ( v1_tsep_1(B_357,B_357)
      | ~ v3_pre_topc(u1_struct_0(B_357),B_357)
      | ~ m1_pre_topc(B_357,B_357)
      | ~ l1_pre_topc(B_357)
      | ~ v2_pre_topc(B_357) ) ),
    inference(resolution,[status(thm)],[c_83,c_1670])).

tff(c_1770,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_1756])).

tff(c_1782,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_140,c_1019,c_1770])).

tff(c_1787,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1782])).

tff(c_1836,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_571,c_1787])).

tff(c_1849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_140,c_459,c_1836])).

tff(c_1851,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1782])).

tff(c_1850,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1782])).

tff(c_180,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_171])).

tff(c_187,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_180])).

tff(c_34,plain,(
    ! [B_27,A_25] :
      ( m1_subset_1(u1_struct_0(B_27),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1935,plain,(
    ! [B_360,A_361] :
      ( v3_pre_topc(u1_struct_0(B_360),A_361)
      | ~ v1_tsep_1(B_360,A_361)
      | ~ m1_subset_1(u1_struct_0(B_360),k1_zfmisc_1(u1_struct_0(A_361)))
      | ~ m1_pre_topc(B_360,A_361)
      | ~ l1_pre_topc(A_361)
      | ~ v2_pre_topc(A_361) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2172,plain,(
    ! [B_370,A_371] :
      ( v3_pre_topc(u1_struct_0(B_370),A_371)
      | ~ v1_tsep_1(B_370,A_371)
      | ~ v2_pre_topc(A_371)
      | ~ m1_pre_topc(B_370,A_371)
      | ~ l1_pre_topc(A_371) ) ),
    inference(resolution,[status(thm)],[c_34,c_1935])).

tff(c_216,plain,(
    ! [B_294] :
      ( m1_subset_1(u1_struct_0(B_294),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_294,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_200])).

tff(c_1008,plain,(
    ! [B_294] :
      ( v3_pre_topc(u1_struct_0(B_294),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_294),'#skF_3')
      | ~ m1_pre_topc(B_294,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_216,c_996])).

tff(c_2184,plain,(
    ! [B_370] :
      ( v3_pre_topc(u1_struct_0(B_370),'#skF_4')
      | ~ v1_tsep_1(B_370,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_370,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2172,c_1008])).

tff(c_2203,plain,(
    ! [B_370] :
      ( v3_pre_topc(u1_struct_0(B_370),'#skF_4')
      | ~ v1_tsep_1(B_370,'#skF_3')
      | ~ m1_pre_topc(B_370,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_184,c_2184])).

tff(c_2228,plain,(
    ! [B_373,A_374] :
      ( v1_tsep_1(B_373,A_374)
      | ~ v3_pre_topc(u1_struct_0(B_373),A_374)
      | ~ v2_pre_topc(A_374)
      | ~ m1_pre_topc(B_373,A_374)
      | ~ l1_pre_topc(A_374) ) ),
    inference(resolution,[status(thm)],[c_34,c_1670])).

tff(c_2231,plain,(
    ! [B_370] :
      ( v1_tsep_1(B_370,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_370,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tsep_1(B_370,'#skF_3')
      | ~ m1_pre_topc(B_370,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2203,c_2228])).

tff(c_2266,plain,(
    ! [B_375] :
      ( v1_tsep_1(B_375,'#skF_4')
      | ~ m1_pre_topc(B_375,'#skF_4')
      | ~ v1_tsep_1(B_375,'#skF_3')
      | ~ m1_pre_topc(B_375,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_187,c_2231])).

tff(c_2269,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1850,c_2266])).

tff(c_2272,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_556,c_2269])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_160,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_52])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_81,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50])).

tff(c_153,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_81])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_3038,plain,(
    ! [G_420,D_416,E_419,A_418,B_417,C_415] :
      ( r1_tmap_1(D_416,B_417,E_419,G_420)
      | ~ r1_tmap_1(C_415,B_417,k3_tmap_1(A_418,B_417,D_416,C_415,E_419),G_420)
      | ~ m1_subset_1(G_420,u1_struct_0(C_415))
      | ~ m1_subset_1(G_420,u1_struct_0(D_416))
      | ~ m1_pre_topc(C_415,D_416)
      | ~ v1_tsep_1(C_415,D_416)
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_416),u1_struct_0(B_417))))
      | ~ v1_funct_2(E_419,u1_struct_0(D_416),u1_struct_0(B_417))
      | ~ v1_funct_1(E_419)
      | ~ m1_pre_topc(D_416,A_418)
      | v2_struct_0(D_416)
      | ~ m1_pre_topc(C_415,A_418)
      | v2_struct_0(C_415)
      | ~ l1_pre_topc(B_417)
      | ~ v2_pre_topc(B_417)
      | v2_struct_0(B_417)
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418)
      | v2_struct_0(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_3040,plain,
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
    inference(resolution,[status(thm)],[c_82,c_3038])).

tff(c_3043,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_169,c_116,c_151,c_159,c_116,c_151,c_2272,c_556,c_160,c_151,c_153,c_147,c_3040])).

tff(c_3045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_3043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.48/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.01  
% 5.48/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.01  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.48/2.01  
% 5.48/2.01  %Foreground sorts:
% 5.48/2.01  
% 5.48/2.01  
% 5.48/2.01  %Background operators:
% 5.48/2.01  
% 5.48/2.01  
% 5.48/2.01  %Foreground operators:
% 5.48/2.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.48/2.01  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.48/2.01  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.48/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.48/2.01  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.48/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.48/2.01  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.48/2.01  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.48/2.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.48/2.01  tff('#skF_7', type, '#skF_7': $i).
% 5.48/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.48/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.48/2.01  tff('#skF_6', type, '#skF_6': $i).
% 5.48/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.48/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.48/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.48/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.48/2.01  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.48/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.48/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.48/2.01  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.48/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.48/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.48/2.01  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.48/2.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.48/2.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.48/2.01  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.48/2.01  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.48/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.48/2.01  
% 5.48/2.04  tff(f_221, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.48/2.04  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.48/2.04  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.48/2.04  tff(f_42, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.48/2.04  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.48/2.04  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.48/2.04  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.48/2.04  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.48/2.04  tff(f_122, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 5.48/2.04  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.48/2.04  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.48/2.04  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.48/2.04  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 5.48/2.04  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.48/2.04  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 5.48/2.04  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_127, plain, (![B_289, A_290]: (l1_pre_topc(B_289) | ~m1_pre_topc(B_289, A_290) | ~l1_pre_topc(A_290))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.48/2.04  tff(c_136, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_127])).
% 5.48/2.04  tff(c_143, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_136])).
% 5.48/2.04  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.48/2.04  tff(c_104, plain, (![A_287]: (u1_struct_0(A_287)=k2_struct_0(A_287) | ~l1_struct_0(A_287))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.48/2.04  tff(c_108, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_10, c_104])).
% 5.48/2.04  tff(c_151, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_143, c_108])).
% 5.48/2.04  tff(c_109, plain, (![A_288]: (u1_struct_0(A_288)=k2_struct_0(A_288) | ~l1_pre_topc(A_288))), inference(resolution, [status(thm)], [c_10, c_104])).
% 5.48/2.04  tff(c_116, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_109])).
% 5.48/2.04  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_118, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_58])).
% 5.48/2.04  tff(c_169, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_118])).
% 5.48/2.04  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_158, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_56])).
% 5.48/2.04  tff(c_159, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_158])).
% 5.48/2.04  tff(c_171, plain, (![B_292, A_293]: (v2_pre_topc(B_292) | ~m1_pre_topc(B_292, A_293) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.48/2.04  tff(c_177, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_171])).
% 5.48/2.04  tff(c_184, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_177])).
% 5.48/2.04  tff(c_133, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_127])).
% 5.48/2.04  tff(c_140, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_133])).
% 5.48/2.04  tff(c_36, plain, (![A_28]: (m1_pre_topc(A_28, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.48/2.04  tff(c_147, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_140, c_108])).
% 5.48/2.04  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_152, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_147, c_54])).
% 5.48/2.04  tff(c_302, plain, (![A_304, B_305]: (m1_pre_topc(A_304, B_305) | ~m1_pre_topc(A_304, g1_pre_topc(u1_struct_0(B_305), u1_pre_topc(B_305))) | ~l1_pre_topc(B_305) | ~l1_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.48/2.04  tff(c_308, plain, (![A_304]: (m1_pre_topc(A_304, '#skF_3') | ~m1_pre_topc(A_304, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_304))), inference(superposition, [status(thm), theory('equality')], [c_147, c_302])).
% 5.48/2.04  tff(c_322, plain, (![A_304]: (m1_pre_topc(A_304, '#skF_3') | ~m1_pre_topc(A_304, '#skF_4') | ~l1_pre_topc(A_304))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_152, c_308])).
% 5.48/2.04  tff(c_188, plain, (![B_294, A_295]: (m1_subset_1(u1_struct_0(B_294), k1_zfmisc_1(u1_struct_0(A_295))) | ~m1_pre_topc(B_294, A_295) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.48/2.04  tff(c_200, plain, (![B_294]: (m1_subset_1(u1_struct_0(B_294), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_294, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_188])).
% 5.48/2.04  tff(c_277, plain, (![B_302]: (m1_subset_1(u1_struct_0(B_302), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_302, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_200])).
% 5.48/2.04  tff(c_280, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_151, c_277])).
% 5.48/2.04  tff(c_401, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_280])).
% 5.48/2.04  tff(c_447, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_322, c_401])).
% 5.48/2.04  tff(c_450, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_447])).
% 5.48/2.04  tff(c_453, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_450])).
% 5.48/2.04  tff(c_457, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_453])).
% 5.48/2.04  tff(c_459, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_280])).
% 5.48/2.04  tff(c_194, plain, (![B_294]: (m1_subset_1(u1_struct_0(B_294), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_294, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_151, c_188])).
% 5.48/2.04  tff(c_221, plain, (![B_296]: (m1_subset_1(u1_struct_0(B_296), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_296, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_194])).
% 5.48/2.04  tff(c_227, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_147, c_221])).
% 5.48/2.04  tff(c_477, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_227])).
% 5.48/2.04  tff(c_478, plain, (![A_311, B_312]: (m1_pre_topc(A_311, g1_pre_topc(u1_struct_0(B_312), u1_pre_topc(B_312))) | ~m1_pre_topc(A_311, B_312) | ~l1_pre_topc(B_312) | ~l1_pre_topc(A_311))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.48/2.04  tff(c_499, plain, (![A_311]: (m1_pre_topc(A_311, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_311, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_311))), inference(superposition, [status(thm), theory('equality')], [c_147, c_478])).
% 5.48/2.04  tff(c_527, plain, (![A_313]: (m1_pre_topc(A_313, '#skF_4') | ~m1_pre_topc(A_313, '#skF_3') | ~l1_pre_topc(A_313))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_152, c_499])).
% 5.48/2.04  tff(c_541, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_527])).
% 5.48/2.04  tff(c_552, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_541])).
% 5.48/2.04  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_552])).
% 5.48/2.04  tff(c_556, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_227])).
% 5.48/2.04  tff(c_38, plain, (![C_35, A_29, B_33]: (m1_pre_topc(C_35, A_29) | ~m1_pre_topc(C_35, B_33) | ~m1_pre_topc(B_33, A_29) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.48/2.04  tff(c_571, plain, (![A_29]: (m1_pre_topc('#skF_3', A_29) | ~m1_pre_topc('#skF_4', A_29) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29))), inference(resolution, [status(thm)], [c_556, c_38])).
% 5.48/2.04  tff(c_26, plain, (![A_17]: (v3_pre_topc(k2_struct_0(A_17), A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.48/2.04  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.48/2.04  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.48/2.04  tff(c_83, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.48/2.04  tff(c_975, plain, (![B_328, A_329]: (v3_pre_topc(B_328, g1_pre_topc(u1_struct_0(A_329), u1_pre_topc(A_329))) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0(A_329))) | ~v3_pre_topc(B_328, A_329) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.48/2.04  tff(c_981, plain, (![B_328]: (v3_pre_topc(B_328, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_328, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_147, c_975])).
% 5.48/2.04  tff(c_996, plain, (![B_330]: (v3_pre_topc(B_330, '#skF_4') | ~m1_subset_1(B_330, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_330, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_140, c_147, c_152, c_981])).
% 5.48/2.04  tff(c_1009, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_83, c_996])).
% 5.48/2.04  tff(c_1010, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1009])).
% 5.48/2.04  tff(c_1013, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1010])).
% 5.48/2.04  tff(c_1017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_140, c_1013])).
% 5.48/2.04  tff(c_1019, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_1009])).
% 5.48/2.04  tff(c_1670, plain, (![B_353, A_354]: (v1_tsep_1(B_353, A_354) | ~v3_pre_topc(u1_struct_0(B_353), A_354) | ~m1_subset_1(u1_struct_0(B_353), k1_zfmisc_1(u1_struct_0(A_354))) | ~m1_pre_topc(B_353, A_354) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.48/2.04  tff(c_1756, plain, (![B_357]: (v1_tsep_1(B_357, B_357) | ~v3_pre_topc(u1_struct_0(B_357), B_357) | ~m1_pre_topc(B_357, B_357) | ~l1_pre_topc(B_357) | ~v2_pre_topc(B_357))), inference(resolution, [status(thm)], [c_83, c_1670])).
% 5.48/2.04  tff(c_1770, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_147, c_1756])).
% 5.48/2.04  tff(c_1782, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_140, c_1019, c_1770])).
% 5.48/2.04  tff(c_1787, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_1782])).
% 5.48/2.04  tff(c_1836, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_571, c_1787])).
% 5.48/2.04  tff(c_1849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_140, c_459, c_1836])).
% 5.48/2.04  tff(c_1851, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_1782])).
% 5.48/2.04  tff(c_1850, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_1782])).
% 5.48/2.04  tff(c_180, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_171])).
% 5.48/2.04  tff(c_187, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_180])).
% 5.48/2.04  tff(c_34, plain, (![B_27, A_25]: (m1_subset_1(u1_struct_0(B_27), k1_zfmisc_1(u1_struct_0(A_25))) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.48/2.04  tff(c_1935, plain, (![B_360, A_361]: (v3_pre_topc(u1_struct_0(B_360), A_361) | ~v1_tsep_1(B_360, A_361) | ~m1_subset_1(u1_struct_0(B_360), k1_zfmisc_1(u1_struct_0(A_361))) | ~m1_pre_topc(B_360, A_361) | ~l1_pre_topc(A_361) | ~v2_pre_topc(A_361))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.48/2.04  tff(c_2172, plain, (![B_370, A_371]: (v3_pre_topc(u1_struct_0(B_370), A_371) | ~v1_tsep_1(B_370, A_371) | ~v2_pre_topc(A_371) | ~m1_pre_topc(B_370, A_371) | ~l1_pre_topc(A_371))), inference(resolution, [status(thm)], [c_34, c_1935])).
% 5.48/2.04  tff(c_216, plain, (![B_294]: (m1_subset_1(u1_struct_0(B_294), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_294, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_200])).
% 5.48/2.04  tff(c_1008, plain, (![B_294]: (v3_pre_topc(u1_struct_0(B_294), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_294), '#skF_3') | ~m1_pre_topc(B_294, '#skF_3'))), inference(resolution, [status(thm)], [c_216, c_996])).
% 5.48/2.04  tff(c_2184, plain, (![B_370]: (v3_pre_topc(u1_struct_0(B_370), '#skF_4') | ~v1_tsep_1(B_370, '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc(B_370, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_2172, c_1008])).
% 5.48/2.04  tff(c_2203, plain, (![B_370]: (v3_pre_topc(u1_struct_0(B_370), '#skF_4') | ~v1_tsep_1(B_370, '#skF_3') | ~m1_pre_topc(B_370, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_184, c_2184])).
% 5.48/2.04  tff(c_2228, plain, (![B_373, A_374]: (v1_tsep_1(B_373, A_374) | ~v3_pre_topc(u1_struct_0(B_373), A_374) | ~v2_pre_topc(A_374) | ~m1_pre_topc(B_373, A_374) | ~l1_pre_topc(A_374))), inference(resolution, [status(thm)], [c_34, c_1670])).
% 5.48/2.04  tff(c_2231, plain, (![B_370]: (v1_tsep_1(B_370, '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc(B_370, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tsep_1(B_370, '#skF_3') | ~m1_pre_topc(B_370, '#skF_3'))), inference(resolution, [status(thm)], [c_2203, c_2228])).
% 5.48/2.04  tff(c_2266, plain, (![B_375]: (v1_tsep_1(B_375, '#skF_4') | ~m1_pre_topc(B_375, '#skF_4') | ~v1_tsep_1(B_375, '#skF_3') | ~m1_pre_topc(B_375, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_187, c_2231])).
% 5.48/2.04  tff(c_2269, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1850, c_2266])).
% 5.48/2.04  tff(c_2272, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_556, c_2269])).
% 5.48/2.04  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_160, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_52])).
% 5.48/2.04  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_81, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50])).
% 5.48/2.04  tff(c_153, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_81])).
% 5.48/2.04  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_221])).
% 5.48/2.04  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 5.48/2.04  tff(c_3038, plain, (![G_420, D_416, E_419, A_418, B_417, C_415]: (r1_tmap_1(D_416, B_417, E_419, G_420) | ~r1_tmap_1(C_415, B_417, k3_tmap_1(A_418, B_417, D_416, C_415, E_419), G_420) | ~m1_subset_1(G_420, u1_struct_0(C_415)) | ~m1_subset_1(G_420, u1_struct_0(D_416)) | ~m1_pre_topc(C_415, D_416) | ~v1_tsep_1(C_415, D_416) | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_416), u1_struct_0(B_417)))) | ~v1_funct_2(E_419, u1_struct_0(D_416), u1_struct_0(B_417)) | ~v1_funct_1(E_419) | ~m1_pre_topc(D_416, A_418) | v2_struct_0(D_416) | ~m1_pre_topc(C_415, A_418) | v2_struct_0(C_415) | ~l1_pre_topc(B_417) | ~v2_pre_topc(B_417) | v2_struct_0(B_417) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418) | v2_struct_0(A_418))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.48/2.04  tff(c_3040, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_3038])).
% 5.48/2.04  tff(c_3043, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_169, c_116, c_151, c_159, c_116, c_151, c_2272, c_556, c_160, c_151, c_153, c_147, c_3040])).
% 5.48/2.04  tff(c_3045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_3043])).
% 5.48/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.04  
% 5.48/2.04  Inference rules
% 5.48/2.04  ----------------------
% 5.48/2.04  #Ref     : 0
% 5.48/2.04  #Sup     : 571
% 5.48/2.04  #Fact    : 0
% 5.48/2.04  #Define  : 0
% 5.48/2.04  #Split   : 32
% 5.48/2.04  #Chain   : 0
% 5.48/2.04  #Close   : 0
% 5.48/2.04  
% 5.48/2.04  Ordering : KBO
% 5.48/2.04  
% 5.48/2.04  Simplification rules
% 5.48/2.04  ----------------------
% 5.48/2.04  #Subsume      : 130
% 5.48/2.04  #Demod        : 846
% 5.48/2.04  #Tautology    : 168
% 5.48/2.04  #SimpNegUnit  : 20
% 5.48/2.04  #BackRed      : 5
% 5.48/2.04  
% 5.48/2.04  #Partial instantiations: 0
% 5.48/2.04  #Strategies tried      : 1
% 5.48/2.04  
% 5.48/2.04  Timing (in seconds)
% 5.48/2.04  ----------------------
% 5.79/2.04  Preprocessing        : 0.41
% 5.79/2.04  Parsing              : 0.21
% 5.79/2.04  CNF conversion       : 0.05
% 5.79/2.04  Main loop            : 0.78
% 5.79/2.04  Inferencing          : 0.24
% 5.79/2.04  Reduction            : 0.31
% 5.79/2.04  Demodulation         : 0.23
% 5.79/2.04  BG Simplification    : 0.03
% 5.79/2.04  Subsumption          : 0.15
% 5.79/2.04  Abstraction          : 0.03
% 5.79/2.04  MUC search           : 0.00
% 5.79/2.04  Cooper               : 0.00
% 5.79/2.04  Total                : 1.24
% 5.79/2.04  Index Insertion      : 0.00
% 5.79/2.04  Index Deletion       : 0.00
% 5.79/2.04  Index Matching       : 0.00
% 5.79/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
