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
% DateTime   : Thu Dec  3 10:27:38 EST 2020

% Result     : Theorem 9.37s
% Output     : CNFRefutation 9.60s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 740 expanded)
%              Number of leaves         :   44 ( 274 expanded)
%              Depth                    :   17
%              Number of atoms          :  266 (3281 expanded)
%              Number of equality atoms :   19 ( 371 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_223,negated_conjecture,(
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

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_174,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_101,axiom,(
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

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_46,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_80,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_68,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_120,plain,(
    ! [B_290,A_291] :
      ( l1_pre_topc(B_290)
      | ~ m1_pre_topc(B_290,A_291)
      | ~ l1_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_129,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_120])).

tff(c_136,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_129])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [A_288] :
      ( u1_struct_0(A_288) = k2_struct_0(A_288)
      | ~ l1_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_97,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_93])).

tff(c_144,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_97])).

tff(c_102,plain,(
    ! [A_289] :
      ( u1_struct_0(A_289) = k2_struct_0(A_289)
      | ~ l1_pre_topc(A_289) ) ),
    inference(resolution,[status(thm)],[c_16,c_93])).

tff(c_109,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_102])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_111,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_60])).

tff(c_153,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_111])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_151,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_58])).

tff(c_152,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_151])).

tff(c_126,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_133,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_126])).

tff(c_140,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_201,plain,(
    ! [B_301,A_302] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ m1_pre_topc(B_301,A_302)
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_210,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_301,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_201])).

tff(c_238,plain,(
    ! [B_303] :
      ( m1_subset_1(u1_struct_0(B_303),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_303,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_210])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_255,plain,(
    ! [B_304] :
      ( r1_tarski(u1_struct_0(B_304),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_304,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_238,c_8])).

tff(c_263,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_255])).

tff(c_272,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_38,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_145,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_56])).

tff(c_672,plain,(
    ! [A_326,B_327] :
      ( m1_pre_topc(A_326,g1_pre_topc(u1_struct_0(B_327),u1_pre_topc(B_327)))
      | ~ m1_pre_topc(A_326,B_327)
      | ~ l1_pre_topc(B_327)
      | ~ l1_pre_topc(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_699,plain,(
    ! [A_326] :
      ( m1_pre_topc(A_326,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_326,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_672])).

tff(c_725,plain,(
    ! [A_328] :
      ( m1_pre_topc(A_328,'#skF_4')
      | ~ m1_pre_topc(A_328,'#skF_3')
      | ~ l1_pre_topc(A_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_145,c_699])).

tff(c_743,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_725])).

tff(c_757,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_743])).

tff(c_759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_757])).

tff(c_761,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_154,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_54])).

tff(c_760,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_855,plain,(
    ! [B_333,A_334] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_333),u1_pre_topc(B_333)),A_334)
      | ~ m1_pre_topc(B_333,A_334)
      | ~ l1_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_869,plain,(
    ! [A_334] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_334)
      | ~ m1_pre_topc('#skF_3',A_334)
      | ~ l1_pre_topc(A_334) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_855])).

tff(c_880,plain,(
    ! [A_335] :
      ( m1_pre_topc('#skF_4',A_335)
      | ~ m1_pre_topc('#skF_3',A_335)
      | ~ l1_pre_topc(A_335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_869])).

tff(c_887,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_880])).

tff(c_896,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_887])).

tff(c_216,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_301,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_201])).

tff(c_1043,plain,(
    ! [B_343] :
      ( m1_subset_1(u1_struct_0(B_343),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_343,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_216])).

tff(c_1049,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1043])).

tff(c_1061,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_896,c_1049])).

tff(c_1065,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1061,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1109,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1065,c_2])).

tff(c_1112,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_1109])).

tff(c_1121,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_140])).

tff(c_50,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_48,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_84,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_1736,plain,(
    ! [G_375,A_373,E_377,C_374,D_378,B_376] :
      ( r1_tmap_1(D_378,B_376,E_377,G_375)
      | ~ r1_tmap_1(C_374,B_376,k3_tmap_1(A_373,B_376,D_378,C_374,E_377),G_375)
      | ~ m1_subset_1(G_375,u1_struct_0(C_374))
      | ~ m1_subset_1(G_375,u1_struct_0(D_378))
      | ~ m1_pre_topc(C_374,D_378)
      | ~ v1_tsep_1(C_374,D_378)
      | ~ m1_subset_1(E_377,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_378),u1_struct_0(B_376))))
      | ~ v1_funct_2(E_377,u1_struct_0(D_378),u1_struct_0(B_376))
      | ~ v1_funct_1(E_377)
      | ~ m1_pre_topc(D_378,A_373)
      | v2_struct_0(D_378)
      | ~ m1_pre_topc(C_374,A_373)
      | v2_struct_0(C_374)
      | ~ l1_pre_topc(B_376)
      | ~ v2_pre_topc(B_376)
      | v2_struct_0(B_376)
      | ~ l1_pre_topc(A_373)
      | ~ v2_pre_topc(A_373)
      | v2_struct_0(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1738,plain,
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
    inference(resolution,[status(thm)],[c_84,c_1736])).

tff(c_1741,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_68,c_64,c_62,c_153,c_109,c_144,c_152,c_109,c_144,c_761,c_154,c_144,c_154,c_1121,c_1738])).

tff(c_1742,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_70,c_66,c_46,c_1741])).

tff(c_184,plain,(
    ! [B_299,A_300] :
      ( v2_pre_topc(B_299)
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_193,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_184])).

tff(c_200,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_193])).

tff(c_24,plain,(
    ! [A_16] :
      ( v3_pre_topc(k2_struct_0(A_16),A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1391,plain,(
    ! [B_353,A_354] :
      ( v1_tsep_1(B_353,A_354)
      | ~ v3_pre_topc(u1_struct_0(B_353),A_354)
      | ~ m1_subset_1(u1_struct_0(B_353),k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ m1_pre_topc(B_353,A_354)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1982,plain,(
    ! [B_394,A_395] :
      ( v1_tsep_1(B_394,A_395)
      | ~ v3_pre_topc(u1_struct_0(B_394),A_395)
      | ~ v2_pre_topc(A_395)
      | ~ m1_pre_topc(B_394,A_395)
      | ~ l1_pre_topc(A_395) ) ),
    inference(resolution,[status(thm)],[c_36,c_1391])).

tff(c_14145,plain,(
    ! [A_672] :
      ( v1_tsep_1('#skF_3',A_672)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_672)
      | ~ v2_pre_topc(A_672)
      | ~ m1_pre_topc('#skF_3',A_672)
      | ~ l1_pre_topc(A_672) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_1982])).

tff(c_14161,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_14145])).

tff(c_14172,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_136,c_761,c_14161])).

tff(c_14174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1742,c_14172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.37/3.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.37/3.69  
% 9.37/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.37/3.69  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.37/3.69  
% 9.37/3.69  %Foreground sorts:
% 9.37/3.69  
% 9.37/3.69  
% 9.37/3.69  %Background operators:
% 9.37/3.69  
% 9.37/3.69  
% 9.37/3.69  %Foreground operators:
% 9.37/3.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.37/3.69  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 9.37/3.69  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.37/3.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.37/3.69  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.37/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.37/3.69  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.37/3.69  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 9.37/3.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.37/3.69  tff('#skF_7', type, '#skF_7': $i).
% 9.37/3.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.37/3.69  tff('#skF_5', type, '#skF_5': $i).
% 9.37/3.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.37/3.69  tff('#skF_6', type, '#skF_6': $i).
% 9.37/3.69  tff('#skF_2', type, '#skF_2': $i).
% 9.37/3.69  tff('#skF_3', type, '#skF_3': $i).
% 9.37/3.69  tff('#skF_1', type, '#skF_1': $i).
% 9.37/3.69  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.37/3.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.37/3.69  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.37/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.37/3.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.37/3.69  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 9.37/3.69  tff('#skF_4', type, '#skF_4': $i).
% 9.37/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.37/3.69  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.37/3.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.37/3.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.37/3.69  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.37/3.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.37/3.69  
% 9.60/3.71  tff(f_223, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 9.60/3.71  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.60/3.71  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.60/3.71  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.60/3.71  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.60/3.71  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.60/3.71  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.60/3.71  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 9.60/3.71  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 9.60/3.71  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.60/3.71  tff(f_174, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 9.60/3.71  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 9.60/3.71  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 9.60/3.71  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 9.60/3.71  tff(c_82, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_46, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_80, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_68, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_120, plain, (![B_290, A_291]: (l1_pre_topc(B_290) | ~m1_pre_topc(B_290, A_291) | ~l1_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.60/3.71  tff(c_129, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_120])).
% 9.60/3.71  tff(c_136, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_129])).
% 9.60/3.71  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.60/3.71  tff(c_93, plain, (![A_288]: (u1_struct_0(A_288)=k2_struct_0(A_288) | ~l1_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.60/3.71  tff(c_97, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_16, c_93])).
% 9.60/3.71  tff(c_144, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_136, c_97])).
% 9.60/3.71  tff(c_102, plain, (![A_289]: (u1_struct_0(A_289)=k2_struct_0(A_289) | ~l1_pre_topc(A_289))), inference(resolution, [status(thm)], [c_16, c_93])).
% 9.60/3.71  tff(c_109, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_102])).
% 9.60/3.71  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_111, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_60])).
% 9.60/3.71  tff(c_153, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_111])).
% 9.60/3.71  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_151, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_58])).
% 9.60/3.71  tff(c_152, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_151])).
% 9.60/3.71  tff(c_126, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_120])).
% 9.60/3.71  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_126])).
% 9.60/3.71  tff(c_140, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_97])).
% 9.60/3.71  tff(c_201, plain, (![B_301, A_302]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(u1_struct_0(A_302))) | ~m1_pre_topc(B_301, A_302) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.60/3.71  tff(c_210, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_301, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_201])).
% 9.60/3.71  tff(c_238, plain, (![B_303]: (m1_subset_1(u1_struct_0(B_303), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_303, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_210])).
% 9.60/3.71  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.60/3.71  tff(c_255, plain, (![B_304]: (r1_tarski(u1_struct_0(B_304), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_304, '#skF_4'))), inference(resolution, [status(thm)], [c_238, c_8])).
% 9.60/3.71  tff(c_263, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_140, c_255])).
% 9.60/3.71  tff(c_272, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_263])).
% 9.60/3.71  tff(c_38, plain, (![A_30]: (m1_pre_topc(A_30, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.60/3.71  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_145, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_56])).
% 9.60/3.71  tff(c_672, plain, (![A_326, B_327]: (m1_pre_topc(A_326, g1_pre_topc(u1_struct_0(B_327), u1_pre_topc(B_327))) | ~m1_pre_topc(A_326, B_327) | ~l1_pre_topc(B_327) | ~l1_pre_topc(A_326))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.60/3.71  tff(c_699, plain, (![A_326]: (m1_pre_topc(A_326, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_326, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_326))), inference(superposition, [status(thm), theory('equality')], [c_140, c_672])).
% 9.60/3.71  tff(c_725, plain, (![A_328]: (m1_pre_topc(A_328, '#skF_4') | ~m1_pre_topc(A_328, '#skF_3') | ~l1_pre_topc(A_328))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_145, c_699])).
% 9.60/3.71  tff(c_743, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_725])).
% 9.60/3.71  tff(c_757, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_743])).
% 9.60/3.71  tff(c_759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_757])).
% 9.60/3.71  tff(c_761, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_263])).
% 9.60/3.71  tff(c_54, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_154, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_54])).
% 9.60/3.71  tff(c_760, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_263])).
% 9.60/3.71  tff(c_855, plain, (![B_333, A_334]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_333), u1_pre_topc(B_333)), A_334) | ~m1_pre_topc(B_333, A_334) | ~l1_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.60/3.71  tff(c_869, plain, (![A_334]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_334) | ~m1_pre_topc('#skF_3', A_334) | ~l1_pre_topc(A_334))), inference(superposition, [status(thm), theory('equality')], [c_140, c_855])).
% 9.60/3.71  tff(c_880, plain, (![A_335]: (m1_pre_topc('#skF_4', A_335) | ~m1_pre_topc('#skF_3', A_335) | ~l1_pre_topc(A_335))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_869])).
% 9.60/3.71  tff(c_887, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_38, c_880])).
% 9.60/3.71  tff(c_896, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_887])).
% 9.60/3.71  tff(c_216, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_301, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_201])).
% 9.60/3.71  tff(c_1043, plain, (![B_343]: (m1_subset_1(u1_struct_0(B_343), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_343, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_216])).
% 9.60/3.71  tff(c_1049, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_1043])).
% 9.60/3.71  tff(c_1061, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_896, c_1049])).
% 9.60/3.71  tff(c_1065, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1061, c_8])).
% 9.60/3.71  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.60/3.71  tff(c_1109, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1065, c_2])).
% 9.60/3.71  tff(c_1112, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_1109])).
% 9.60/3.71  tff(c_1121, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1112, c_140])).
% 9.60/3.71  tff(c_50, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_48, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_223])).
% 9.60/3.71  tff(c_84, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 9.60/3.71  tff(c_1736, plain, (![G_375, A_373, E_377, C_374, D_378, B_376]: (r1_tmap_1(D_378, B_376, E_377, G_375) | ~r1_tmap_1(C_374, B_376, k3_tmap_1(A_373, B_376, D_378, C_374, E_377), G_375) | ~m1_subset_1(G_375, u1_struct_0(C_374)) | ~m1_subset_1(G_375, u1_struct_0(D_378)) | ~m1_pre_topc(C_374, D_378) | ~v1_tsep_1(C_374, D_378) | ~m1_subset_1(E_377, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_378), u1_struct_0(B_376)))) | ~v1_funct_2(E_377, u1_struct_0(D_378), u1_struct_0(B_376)) | ~v1_funct_1(E_377) | ~m1_pre_topc(D_378, A_373) | v2_struct_0(D_378) | ~m1_pre_topc(C_374, A_373) | v2_struct_0(C_374) | ~l1_pre_topc(B_376) | ~v2_pre_topc(B_376) | v2_struct_0(B_376) | ~l1_pre_topc(A_373) | ~v2_pre_topc(A_373) | v2_struct_0(A_373))), inference(cnfTransformation, [status(thm)], [f_174])).
% 9.60/3.71  tff(c_1738, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_1736])).
% 9.60/3.71  tff(c_1741, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_68, c_64, c_62, c_153, c_109, c_144, c_152, c_109, c_144, c_761, c_154, c_144, c_154, c_1121, c_1738])).
% 9.60/3.71  tff(c_1742, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_70, c_66, c_46, c_1741])).
% 9.60/3.71  tff(c_184, plain, (![B_299, A_300]: (v2_pre_topc(B_299) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.60/3.71  tff(c_193, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_184])).
% 9.60/3.71  tff(c_200, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_193])).
% 9.60/3.71  tff(c_24, plain, (![A_16]: (v3_pre_topc(k2_struct_0(A_16), A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.60/3.71  tff(c_36, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.60/3.71  tff(c_1391, plain, (![B_353, A_354]: (v1_tsep_1(B_353, A_354) | ~v3_pre_topc(u1_struct_0(B_353), A_354) | ~m1_subset_1(u1_struct_0(B_353), k1_zfmisc_1(u1_struct_0(A_354))) | ~m1_pre_topc(B_353, A_354) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.60/3.71  tff(c_1982, plain, (![B_394, A_395]: (v1_tsep_1(B_394, A_395) | ~v3_pre_topc(u1_struct_0(B_394), A_395) | ~v2_pre_topc(A_395) | ~m1_pre_topc(B_394, A_395) | ~l1_pre_topc(A_395))), inference(resolution, [status(thm)], [c_36, c_1391])).
% 9.60/3.71  tff(c_14145, plain, (![A_672]: (v1_tsep_1('#skF_3', A_672) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_672) | ~v2_pre_topc(A_672) | ~m1_pre_topc('#skF_3', A_672) | ~l1_pre_topc(A_672))), inference(superposition, [status(thm), theory('equality')], [c_1121, c_1982])).
% 9.60/3.71  tff(c_14161, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_14145])).
% 9.60/3.71  tff(c_14172, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_136, c_761, c_14161])).
% 9.60/3.71  tff(c_14174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1742, c_14172])).
% 9.60/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.60/3.71  
% 9.60/3.71  Inference rules
% 9.60/3.71  ----------------------
% 9.60/3.71  #Ref     : 0
% 9.60/3.71  #Sup     : 2930
% 9.60/3.71  #Fact    : 0
% 9.60/3.71  #Define  : 0
% 9.60/3.71  #Split   : 24
% 9.60/3.71  #Chain   : 0
% 9.60/3.71  #Close   : 0
% 9.60/3.71  
% 9.60/3.71  Ordering : KBO
% 9.60/3.71  
% 9.60/3.71  Simplification rules
% 9.60/3.71  ----------------------
% 9.60/3.71  #Subsume      : 712
% 9.60/3.71  #Demod        : 5730
% 9.60/3.71  #Tautology    : 767
% 9.60/3.71  #SimpNegUnit  : 100
% 9.60/3.71  #BackRed      : 18
% 9.60/3.71  
% 9.60/3.71  #Partial instantiations: 0
% 9.60/3.71  #Strategies tried      : 1
% 9.60/3.71  
% 9.60/3.71  Timing (in seconds)
% 9.60/3.71  ----------------------
% 9.60/3.71  Preprocessing        : 0.40
% 9.60/3.71  Parsing              : 0.21
% 9.60/3.71  CNF conversion       : 0.05
% 9.60/3.71  Main loop            : 2.49
% 9.60/3.71  Inferencing          : 0.58
% 9.60/3.71  Reduction            : 1.11
% 9.60/3.71  Demodulation         : 0.89
% 9.60/3.71  BG Simplification    : 0.06
% 9.60/3.71  Subsumption          : 0.60
% 9.60/3.71  Abstraction          : 0.09
% 9.60/3.71  MUC search           : 0.00
% 9.60/3.71  Cooper               : 0.00
% 9.60/3.71  Total                : 2.93
% 9.60/3.71  Index Insertion      : 0.00
% 9.60/3.71  Index Deletion       : 0.00
% 9.60/3.71  Index Matching       : 0.00
% 9.60/3.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
