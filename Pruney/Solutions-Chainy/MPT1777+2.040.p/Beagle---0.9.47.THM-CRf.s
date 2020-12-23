%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:38 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  141 (1795 expanded)
%              Number of leaves         :   45 ( 645 expanded)
%              Depth                    :   25
%              Number of atoms          :  303 (8801 expanded)
%              Number of equality atoms :   18 ( 978 expanded)
%              Maximal formula depth    :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_237,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_119,axiom,(
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

tff(f_188,axiom,(
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
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( v3_pre_topc(F,D)
                                        & r2_hidden(G,F)
                                        & r1_tarski(F,u1_struct_0(C))
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_120,plain,(
    ! [B_421,A_422] :
      ( l1_pre_topc(B_421)
      | ~ m1_pre_topc(B_421,A_422)
      | ~ l1_pre_topc(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_129,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_120])).

tff(c_136,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_129])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_93,plain,(
    ! [A_419] :
      ( u1_struct_0(A_419) = k2_struct_0(A_419)
      | ~ l1_struct_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_93])).

tff(c_144,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_97])).

tff(c_163,plain,(
    ! [A_423] :
      ( ~ v1_xboole_0(u1_struct_0(A_423))
      | ~ l1_struct_0(A_423)
      | v2_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_166,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_163])).

tff(c_176,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_166])).

tff(c_180,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_183,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_180])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_183])).

tff(c_188,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_154,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_54])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_263,plain,(
    ! [B_435,A_436] :
      ( v2_pre_topc(B_435)
      | ~ m1_pre_topc(B_435,A_436)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_272,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_263])).

tff(c_279,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_272])).

tff(c_32,plain,(
    ! [A_25] :
      ( v3_pre_topc(k2_struct_0(A_25),A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_46,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_68,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_102,plain,(
    ! [A_420] :
      ( u1_struct_0(A_420) = k2_struct_0(A_420)
      | ~ l1_pre_topc(A_420) ) ),
    inference(resolution,[status(thm)],[c_20,c_93])).

tff(c_109,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_102])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_111,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_60])).

tff(c_153,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_111])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

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

tff(c_34,plain,(
    ! [A_26] :
      ( m1_pre_topc(A_26,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_140,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_145,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_56])).

tff(c_530,plain,(
    ! [A_465,B_466] :
      ( m1_pre_topc(A_465,g1_pre_topc(u1_struct_0(B_466),u1_pre_topc(B_466)))
      | ~ m1_pre_topc(A_465,B_466)
      | ~ l1_pre_topc(B_466)
      | ~ l1_pre_topc(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_556,plain,(
    ! [A_465] :
      ( m1_pre_topc(A_465,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_465,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_465) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_530])).

tff(c_582,plain,(
    ! [A_467] :
      ( m1_pre_topc(A_467,'#skF_4')
      | ~ m1_pre_topc(A_467,'#skF_3')
      | ~ l1_pre_topc(A_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_145,c_556])).

tff(c_593,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_582])).

tff(c_600,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_593])).

tff(c_287,plain,(
    ! [B_440,A_441] :
      ( m1_pre_topc(B_440,A_441)
      | ~ m1_pre_topc(B_440,g1_pre_topc(u1_struct_0(A_441),u1_pre_topc(A_441)))
      | ~ l1_pre_topc(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_293,plain,(
    ! [B_440] :
      ( m1_pre_topc(B_440,'#skF_3')
      | ~ m1_pre_topc(B_440,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_287])).

tff(c_307,plain,(
    ! [B_440] :
      ( m1_pre_topc(B_440,'#skF_3')
      | ~ m1_pre_topc(B_440,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_145,c_293])).

tff(c_821,plain,(
    ! [B_474,C_475,A_476] :
      ( r1_tarski(u1_struct_0(B_474),u1_struct_0(C_475))
      | ~ m1_pre_topc(B_474,C_475)
      | ~ m1_pre_topc(C_475,A_476)
      | ~ m1_pre_topc(B_474,A_476)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_843,plain,(
    ! [B_474] :
      ( r1_tarski(u1_struct_0(B_474),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_474,'#skF_3')
      | ~ m1_pre_topc(B_474,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_68,c_821])).

tff(c_870,plain,(
    ! [B_477] :
      ( r1_tarski(u1_struct_0(B_477),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_477,'#skF_3')
      | ~ m1_pre_topc(B_477,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_140,c_843])).

tff(c_877,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_870])).

tff(c_890,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_877])).

tff(c_893,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_890])).

tff(c_920,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_307,c_893])).

tff(c_923,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_920])).

tff(c_927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_923])).

tff(c_928,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_890])).

tff(c_929,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_890])).

tff(c_577,plain,(
    ! [A_465] :
      ( m1_pre_topc(A_465,'#skF_4')
      | ~ m1_pre_topc(A_465,'#skF_3')
      | ~ l1_pre_topc(A_465) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_145,c_556])).

tff(c_934,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_929,c_577])).

tff(c_950,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_934])).

tff(c_36,plain,(
    ! [B_31,C_33,A_27] :
      ( r1_tarski(u1_struct_0(B_31),u1_struct_0(C_33))
      | ~ m1_pre_topc(B_31,C_33)
      | ~ m1_pre_topc(C_33,A_27)
      | ~ m1_pre_topc(B_31,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_962,plain,(
    ! [B_31] :
      ( r1_tarski(u1_struct_0(B_31),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_31,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_950,c_36])).

tff(c_1029,plain,(
    ! [B_483] :
      ( r1_tarski(u1_struct_0(B_483),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_483,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_136,c_144,c_962])).

tff(c_1039,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_1029])).

tff(c_1051,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_1039])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1055,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1051,c_2])).

tff(c_1061,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_1055])).

tff(c_1070,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_140])).

tff(c_50,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_48,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_84,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_1293,plain,(
    ! [C_507,H_502,F_503,A_501,D_504,E_505,B_506] :
      ( r1_tmap_1(D_504,B_506,E_505,H_502)
      | ~ r1_tmap_1(C_507,B_506,k3_tmap_1(A_501,B_506,D_504,C_507,E_505),H_502)
      | ~ r1_tarski(F_503,u1_struct_0(C_507))
      | ~ r2_hidden(H_502,F_503)
      | ~ v3_pre_topc(F_503,D_504)
      | ~ m1_subset_1(H_502,u1_struct_0(C_507))
      | ~ m1_subset_1(H_502,u1_struct_0(D_504))
      | ~ m1_subset_1(F_503,k1_zfmisc_1(u1_struct_0(D_504)))
      | ~ m1_pre_topc(C_507,D_504)
      | ~ m1_subset_1(E_505,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_504),u1_struct_0(B_506))))
      | ~ v1_funct_2(E_505,u1_struct_0(D_504),u1_struct_0(B_506))
      | ~ v1_funct_1(E_505)
      | ~ m1_pre_topc(D_504,A_501)
      | v2_struct_0(D_504)
      | ~ m1_pre_topc(C_507,A_501)
      | v2_struct_0(C_507)
      | ~ l1_pre_topc(B_506)
      | ~ v2_pre_topc(B_506)
      | v2_struct_0(B_506)
      | ~ l1_pre_topc(A_501)
      | ~ v2_pre_topc(A_501)
      | v2_struct_0(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1295,plain,(
    ! [F_503] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_503,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_503)
      | ~ v3_pre_topc(F_503,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_503,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
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
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_84,c_1293])).

tff(c_1298,plain,(
    ! [F_503] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_503,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',F_503)
      | ~ v3_pre_topc(F_503,'#skF_4')
      | ~ m1_subset_1(F_503,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_68,c_64,c_62,c_153,c_109,c_144,c_152,c_109,c_144,c_600,c_144,c_154,c_144,c_154,c_1070,c_1070,c_1295])).

tff(c_1306,plain,(
    ! [F_508] :
      ( ~ r1_tarski(F_508,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',F_508)
      | ~ v3_pre_topc(F_508,'#skF_4')
      | ~ m1_subset_1(F_508,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_70,c_66,c_46,c_1298])).

tff(c_1617,plain,(
    ! [A_528] :
      ( ~ r2_hidden('#skF_6',A_528)
      | ~ v3_pre_topc(A_528,'#skF_4')
      | ~ r1_tarski(A_528,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1306])).

tff(c_1630,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1617])).

tff(c_1683,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1630])).

tff(c_1686,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1683])).

tff(c_1690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_136,c_1686])).

tff(c_1691,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1630])).

tff(c_1695,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_1691])).

tff(c_1698,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_1695])).

tff(c_1700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_1698])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.85  
% 4.45/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.85  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.45/1.85  
% 4.45/1.85  %Foreground sorts:
% 4.45/1.85  
% 4.45/1.85  
% 4.45/1.85  %Background operators:
% 4.45/1.85  
% 4.45/1.85  
% 4.45/1.85  %Foreground operators:
% 4.45/1.85  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.45/1.85  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.45/1.85  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.45/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.45/1.85  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.45/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.85  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.45/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.85  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.45/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.45/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.45/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.45/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.45/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.85  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.45/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.45/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.85  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.45/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.45/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.45/1.85  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.45/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.45/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.85  
% 4.82/1.88  tff(f_237, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.82/1.88  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.82/1.88  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.82/1.88  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.82/1.88  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.82/1.88  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.82/1.88  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.82/1.88  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.82/1.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.82/1.88  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.82/1.88  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.82/1.88  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.82/1.88  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.82/1.88  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.82/1.88  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.82/1.88  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_120, plain, (![B_421, A_422]: (l1_pre_topc(B_421) | ~m1_pre_topc(B_421, A_422) | ~l1_pre_topc(A_422))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.82/1.88  tff(c_129, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_120])).
% 4.82/1.88  tff(c_136, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_129])).
% 4.82/1.88  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.82/1.88  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_93, plain, (![A_419]: (u1_struct_0(A_419)=k2_struct_0(A_419) | ~l1_struct_0(A_419))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.82/1.88  tff(c_97, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_20, c_93])).
% 4.82/1.88  tff(c_144, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_136, c_97])).
% 4.82/1.88  tff(c_163, plain, (![A_423]: (~v1_xboole_0(u1_struct_0(A_423)) | ~l1_struct_0(A_423) | v2_struct_0(A_423))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.82/1.88  tff(c_166, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_144, c_163])).
% 4.82/1.88  tff(c_176, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_66, c_166])).
% 4.82/1.88  tff(c_180, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_176])).
% 4.82/1.88  tff(c_183, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_180])).
% 4.82/1.88  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_183])).
% 4.82/1.88  tff(c_188, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_176])).
% 4.82/1.88  tff(c_54, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_154, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_54])).
% 4.82/1.88  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.82/1.88  tff(c_80, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_263, plain, (![B_435, A_436]: (v2_pre_topc(B_435) | ~m1_pre_topc(B_435, A_436) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.82/1.88  tff(c_272, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_263])).
% 4.82/1.88  tff(c_279, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_272])).
% 4.82/1.88  tff(c_32, plain, (![A_25]: (v3_pre_topc(k2_struct_0(A_25), A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.82/1.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.88  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.82/1.88  tff(c_82, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_46, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_68, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_102, plain, (![A_420]: (u1_struct_0(A_420)=k2_struct_0(A_420) | ~l1_pre_topc(A_420))), inference(resolution, [status(thm)], [c_20, c_93])).
% 4.82/1.88  tff(c_109, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_102])).
% 4.82/1.88  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_111, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_60])).
% 4.82/1.88  tff(c_153, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_111])).
% 4.82/1.88  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_151, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_58])).
% 4.82/1.88  tff(c_152, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_151])).
% 4.82/1.88  tff(c_126, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_120])).
% 4.82/1.88  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_126])).
% 4.82/1.88  tff(c_34, plain, (![A_26]: (m1_pre_topc(A_26, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.82/1.88  tff(c_140, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_97])).
% 4.82/1.88  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_145, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_56])).
% 4.82/1.88  tff(c_530, plain, (![A_465, B_466]: (m1_pre_topc(A_465, g1_pre_topc(u1_struct_0(B_466), u1_pre_topc(B_466))) | ~m1_pre_topc(A_465, B_466) | ~l1_pre_topc(B_466) | ~l1_pre_topc(A_465))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.82/1.88  tff(c_556, plain, (![A_465]: (m1_pre_topc(A_465, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_465, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_465))), inference(superposition, [status(thm), theory('equality')], [c_140, c_530])).
% 4.82/1.88  tff(c_582, plain, (![A_467]: (m1_pre_topc(A_467, '#skF_4') | ~m1_pre_topc(A_467, '#skF_3') | ~l1_pre_topc(A_467))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_145, c_556])).
% 4.82/1.88  tff(c_593, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_582])).
% 4.82/1.88  tff(c_600, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_593])).
% 4.82/1.88  tff(c_287, plain, (![B_440, A_441]: (m1_pre_topc(B_440, A_441) | ~m1_pre_topc(B_440, g1_pre_topc(u1_struct_0(A_441), u1_pre_topc(A_441))) | ~l1_pre_topc(A_441))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.88  tff(c_293, plain, (![B_440]: (m1_pre_topc(B_440, '#skF_3') | ~m1_pre_topc(B_440, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_287])).
% 4.82/1.88  tff(c_307, plain, (![B_440]: (m1_pre_topc(B_440, '#skF_3') | ~m1_pre_topc(B_440, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_145, c_293])).
% 4.82/1.88  tff(c_821, plain, (![B_474, C_475, A_476]: (r1_tarski(u1_struct_0(B_474), u1_struct_0(C_475)) | ~m1_pre_topc(B_474, C_475) | ~m1_pre_topc(C_475, A_476) | ~m1_pre_topc(B_474, A_476) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.82/1.88  tff(c_843, plain, (![B_474]: (r1_tarski(u1_struct_0(B_474), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_474, '#skF_3') | ~m1_pre_topc(B_474, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_821])).
% 4.82/1.88  tff(c_870, plain, (![B_477]: (r1_tarski(u1_struct_0(B_477), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_477, '#skF_3') | ~m1_pre_topc(B_477, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_140, c_843])).
% 4.82/1.88  tff(c_877, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_144, c_870])).
% 4.82/1.88  tff(c_890, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_877])).
% 4.82/1.88  tff(c_893, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_890])).
% 4.82/1.88  tff(c_920, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_307, c_893])).
% 4.82/1.88  tff(c_923, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_920])).
% 4.82/1.88  tff(c_927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_923])).
% 4.82/1.88  tff(c_928, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_890])).
% 4.82/1.88  tff(c_929, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_890])).
% 4.82/1.88  tff(c_577, plain, (![A_465]: (m1_pre_topc(A_465, '#skF_4') | ~m1_pre_topc(A_465, '#skF_3') | ~l1_pre_topc(A_465))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_145, c_556])).
% 4.82/1.88  tff(c_934, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_929, c_577])).
% 4.82/1.88  tff(c_950, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_934])).
% 4.82/1.88  tff(c_36, plain, (![B_31, C_33, A_27]: (r1_tarski(u1_struct_0(B_31), u1_struct_0(C_33)) | ~m1_pre_topc(B_31, C_33) | ~m1_pre_topc(C_33, A_27) | ~m1_pre_topc(B_31, A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.82/1.88  tff(c_962, plain, (![B_31]: (r1_tarski(u1_struct_0(B_31), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_31, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_950, c_36])).
% 4.82/1.88  tff(c_1029, plain, (![B_483]: (r1_tarski(u1_struct_0(B_483), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_483, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_136, c_144, c_962])).
% 4.82/1.88  tff(c_1039, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_140, c_1029])).
% 4.82/1.88  tff(c_1051, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_1039])).
% 4.82/1.88  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.88  tff(c_1055, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1051, c_2])).
% 4.82/1.88  tff(c_1061, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_928, c_1055])).
% 4.82/1.88  tff(c_1070, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_140])).
% 4.82/1.88  tff(c_50, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_48, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.82/1.88  tff(c_84, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 4.82/1.88  tff(c_1293, plain, (![C_507, H_502, F_503, A_501, D_504, E_505, B_506]: (r1_tmap_1(D_504, B_506, E_505, H_502) | ~r1_tmap_1(C_507, B_506, k3_tmap_1(A_501, B_506, D_504, C_507, E_505), H_502) | ~r1_tarski(F_503, u1_struct_0(C_507)) | ~r2_hidden(H_502, F_503) | ~v3_pre_topc(F_503, D_504) | ~m1_subset_1(H_502, u1_struct_0(C_507)) | ~m1_subset_1(H_502, u1_struct_0(D_504)) | ~m1_subset_1(F_503, k1_zfmisc_1(u1_struct_0(D_504))) | ~m1_pre_topc(C_507, D_504) | ~m1_subset_1(E_505, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_504), u1_struct_0(B_506)))) | ~v1_funct_2(E_505, u1_struct_0(D_504), u1_struct_0(B_506)) | ~v1_funct_1(E_505) | ~m1_pre_topc(D_504, A_501) | v2_struct_0(D_504) | ~m1_pre_topc(C_507, A_501) | v2_struct_0(C_507) | ~l1_pre_topc(B_506) | ~v2_pre_topc(B_506) | v2_struct_0(B_506) | ~l1_pre_topc(A_501) | ~v2_pre_topc(A_501) | v2_struct_0(A_501))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.82/1.88  tff(c_1295, plain, (![F_503]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_503, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_503) | ~v3_pre_topc(F_503, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_503, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_1293])).
% 4.82/1.88  tff(c_1298, plain, (![F_503]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_503, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', F_503) | ~v3_pre_topc(F_503, '#skF_4') | ~m1_subset_1(F_503, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_68, c_64, c_62, c_153, c_109, c_144, c_152, c_109, c_144, c_600, c_144, c_154, c_144, c_154, c_1070, c_1070, c_1295])).
% 4.82/1.88  tff(c_1306, plain, (![F_508]: (~r1_tarski(F_508, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', F_508) | ~v3_pre_topc(F_508, '#skF_4') | ~m1_subset_1(F_508, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_70, c_66, c_46, c_1298])).
% 4.82/1.88  tff(c_1617, plain, (![A_528]: (~r2_hidden('#skF_6', A_528) | ~v3_pre_topc(A_528, '#skF_4') | ~r1_tarski(A_528, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_1306])).
% 4.82/1.88  tff(c_1630, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6, c_1617])).
% 4.82/1.88  tff(c_1683, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1630])).
% 4.82/1.88  tff(c_1686, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1683])).
% 4.82/1.88  tff(c_1690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_279, c_136, c_1686])).
% 4.82/1.88  tff(c_1691, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1630])).
% 4.82/1.88  tff(c_1695, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_1691])).
% 4.82/1.88  tff(c_1698, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_1695])).
% 4.82/1.88  tff(c_1700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_1698])).
% 4.82/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.88  
% 4.82/1.88  Inference rules
% 4.82/1.88  ----------------------
% 4.82/1.88  #Ref     : 0
% 4.82/1.88  #Sup     : 340
% 4.82/1.88  #Fact    : 0
% 4.82/1.88  #Define  : 0
% 4.82/1.88  #Split   : 17
% 4.82/1.88  #Chain   : 0
% 4.82/1.88  #Close   : 0
% 4.82/1.88  
% 4.82/1.88  Ordering : KBO
% 4.82/1.88  
% 4.82/1.88  Simplification rules
% 4.82/1.88  ----------------------
% 4.82/1.88  #Subsume      : 51
% 4.82/1.88  #Demod        : 375
% 4.82/1.88  #Tautology    : 114
% 4.82/1.88  #SimpNegUnit  : 14
% 4.82/1.88  #BackRed      : 13
% 4.82/1.88  
% 4.82/1.88  #Partial instantiations: 0
% 4.82/1.88  #Strategies tried      : 1
% 4.82/1.88  
% 4.82/1.88  Timing (in seconds)
% 4.82/1.88  ----------------------
% 4.90/1.88  Preprocessing        : 0.48
% 4.90/1.88  Parsing              : 0.24
% 4.90/1.88  CNF conversion       : 0.07
% 4.90/1.88  Main loop            : 0.57
% 4.90/1.88  Inferencing          : 0.17
% 4.90/1.88  Reduction            : 0.21
% 4.90/1.88  Demodulation         : 0.14
% 4.90/1.88  BG Simplification    : 0.03
% 4.90/1.88  Subsumption          : 0.12
% 4.90/1.88  Abstraction          : 0.03
% 4.90/1.88  MUC search           : 0.00
% 4.90/1.88  Cooper               : 0.00
% 4.90/1.88  Total                : 1.10
% 4.90/1.88  Index Insertion      : 0.00
% 4.90/1.88  Index Deletion       : 0.00
% 4.90/1.88  Index Matching       : 0.00
% 4.90/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
