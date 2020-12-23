%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:35 EST 2020

% Result     : Theorem 10.99s
% Output     : CNFRefutation 11.12s
% Verified   : 
% Statistics : Number of formulae       :  155 (1014 expanded)
%              Number of leaves         :   46 ( 370 expanded)
%              Depth                    :   15
%              Number of atoms          :  387 (4830 expanded)
%              Number of equality atoms :   29 ( 527 expanded)
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

tff(f_277,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_166,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(f_228,axiom,(
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

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_117,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_141,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_82,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_120,plain,(
    ! [B_313,A_314] :
      ( l1_pre_topc(B_313)
      | ~ m1_pre_topc(B_313,A_314)
      | ~ l1_pre_topc(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_120])).

tff(c_133,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_126])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [A_311] :
      ( u1_struct_0(A_311) = k2_struct_0(A_311)
      | ~ l1_struct_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_141,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_102,plain,(
    ! [A_312] :
      ( u1_struct_0(A_312) = k2_struct_0(A_312)
      | ~ l1_pre_topc(A_312) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_110,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_102])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_115,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_62])).

tff(c_147,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_115])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_137,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_60])).

tff(c_146,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_137])).

tff(c_129,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_120])).

tff(c_136,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_129])).

tff(c_145,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_136,c_97])).

tff(c_164,plain,(
    ! [B_316,A_317] :
      ( v2_pre_topc(B_316)
      | ~ m1_pre_topc(B_316,A_317)
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_170,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_164])).

tff(c_177,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_170])).

tff(c_36,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_310,plain,(
    ! [B_324,A_325] :
      ( m1_subset_1(u1_struct_0(B_324),k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ m1_pre_topc(B_324,A_325)
      | ~ l1_pre_topc(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_322,plain,(
    ! [B_324] :
      ( m1_subset_1(u1_struct_0(B_324),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_324,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_310])).

tff(c_457,plain,(
    ! [B_332] :
      ( m1_subset_1(u1_struct_0(B_332),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_332,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_322])).

tff(c_463,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_457])).

tff(c_527,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_530,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_527])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_530])).

tff(c_536,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_557,plain,(
    ! [B_338,C_339,A_340] :
      ( r1_tarski(u1_struct_0(B_338),u1_struct_0(C_339))
      | ~ m1_pre_topc(B_338,C_339)
      | ~ m1_pre_topc(C_339,A_340)
      | ~ m1_pre_topc(B_338,A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_559,plain,(
    ! [B_338] :
      ( r1_tarski(u1_struct_0(B_338),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_338,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_536,c_557])).

tff(c_588,plain,(
    ! [B_341] :
      ( r1_tarski(u1_struct_0(B_341),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_341,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_133,c_141,c_559])).

tff(c_591,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_588])).

tff(c_603,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_153,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_58])).

tff(c_181,plain,(
    ! [A_318] :
      ( g1_pre_topc(u1_struct_0(A_318),u1_pre_topc(A_318)) = A_318
      | ~ v1_pre_topc(A_318)
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_193,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_181])).

tff(c_205,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_193])).

tff(c_211,plain,(
    ~ v1_pre_topc('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_212,plain,(
    ! [A_319] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_319),u1_pre_topc(A_319)))
      | ~ l1_pre_topc(A_319)
      | v2_struct_0(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_218,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_212])).

tff(c_229,plain,
    ( v1_pre_topc('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_153,c_218])).

tff(c_231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_211,c_229])).

tff(c_232,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_1180,plain,(
    ! [D_371,B_372,C_373,A_374] :
      ( m1_pre_topc(D_371,B_372)
      | ~ m1_pre_topc(C_373,A_374)
      | g1_pre_topc(u1_struct_0(D_371),u1_pre_topc(D_371)) != g1_pre_topc(u1_struct_0(C_373),u1_pre_topc(C_373))
      | g1_pre_topc(u1_struct_0(B_372),u1_pre_topc(B_372)) != g1_pre_topc(u1_struct_0(A_374),u1_pre_topc(A_374))
      | ~ l1_pre_topc(D_371)
      | ~ l1_pre_topc(C_373)
      | ~ l1_pre_topc(B_372)
      | ~ l1_pre_topc(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1225,plain,(
    ! [D_371,B_372,A_47] :
      ( m1_pre_topc(D_371,B_372)
      | g1_pre_topc(u1_struct_0(D_371),u1_pre_topc(D_371)) != g1_pre_topc(u1_struct_0(A_47),u1_pre_topc(A_47))
      | g1_pre_topc(u1_struct_0(B_372),u1_pre_topc(B_372)) != g1_pre_topc(u1_struct_0(A_47),u1_pre_topc(A_47))
      | ~ l1_pre_topc(D_371)
      | ~ l1_pre_topc(B_372)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_36,c_1180])).

tff(c_6522,plain,(
    ! [A_529,B_530] :
      ( m1_pre_topc(A_529,B_530)
      | g1_pre_topc(u1_struct_0(B_530),u1_pre_topc(B_530)) != g1_pre_topc(u1_struct_0(A_529),u1_pre_topc(A_529))
      | ~ l1_pre_topc(A_529)
      | ~ l1_pre_topc(B_530)
      | ~ l1_pre_topc(A_529) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1225])).

tff(c_6560,plain,(
    ! [A_529] :
      ( m1_pre_topc(A_529,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_529),u1_pre_topc(A_529)) != g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_529)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_529) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_6522])).

tff(c_6833,plain,(
    ! [A_539] :
      ( m1_pre_topc(A_539,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_539),u1_pre_topc(A_539)) != '#skF_4'
      | ~ l1_pre_topc(A_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_232,c_6560])).

tff(c_6860,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_6833])).

tff(c_6875,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_153,c_6860])).

tff(c_6877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_603,c_6875])).

tff(c_6879,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_148,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_56])).

tff(c_52,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_85,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54])).

tff(c_154,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_85])).

tff(c_50,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_277])).

tff(c_86,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50])).

tff(c_8116,plain,(
    ! [G_592,E_590,B_593,D_588,A_591,C_589] :
      ( r1_tmap_1(D_588,B_593,E_590,G_592)
      | ~ r1_tmap_1(C_589,B_593,k3_tmap_1(A_591,B_593,D_588,C_589,E_590),G_592)
      | ~ m1_subset_1(G_592,u1_struct_0(C_589))
      | ~ m1_subset_1(G_592,u1_struct_0(D_588))
      | ~ m1_pre_topc(C_589,D_588)
      | ~ v1_tsep_1(C_589,D_588)
      | ~ m1_subset_1(E_590,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_588),u1_struct_0(B_593))))
      | ~ v1_funct_2(E_590,u1_struct_0(D_588),u1_struct_0(B_593))
      | ~ v1_funct_1(E_590)
      | ~ m1_pre_topc(D_588,A_591)
      | v2_struct_0(D_588)
      | ~ m1_pre_topc(C_589,A_591)
      | v2_struct_0(C_589)
      | ~ l1_pre_topc(B_593)
      | ~ v2_pre_topc(B_593)
      | v2_struct_0(B_593)
      | ~ l1_pre_topc(A_591)
      | ~ v2_pre_topc(A_591)
      | v2_struct_0(A_591) ) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_8118,plain,
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
    inference(resolution,[status(thm)],[c_86,c_8116])).

tff(c_8121,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_70,c_66,c_64,c_147,c_110,c_141,c_146,c_110,c_141,c_6879,c_148,c_141,c_154,c_145,c_8118])).

tff(c_8122,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_72,c_68,c_48,c_8121])).

tff(c_316,plain,(
    ! [B_324] :
      ( m1_subset_1(u1_struct_0(B_324),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_324,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_310])).

tff(c_471,plain,(
    ! [B_333] :
      ( m1_subset_1(u1_struct_0(B_333),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_333,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_316])).

tff(c_474,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_471])).

tff(c_6920,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_6926,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_6920])).

tff(c_6933,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_6926])).

tff(c_6935,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_173,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_164])).

tff(c_180,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_173])).

tff(c_18,plain,(
    ! [A_26] :
      ( v3_pre_topc(k2_struct_0(A_26),A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [B_46,A_44] :
      ( m1_subset_1(u1_struct_0(B_46),k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ m1_pre_topc(B_46,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_7103,plain,(
    ! [B_548,A_549] :
      ( v1_tsep_1(B_548,A_549)
      | ~ v3_pre_topc(u1_struct_0(B_548),A_549)
      | ~ m1_subset_1(u1_struct_0(B_548),k1_zfmisc_1(u1_struct_0(A_549)))
      | ~ m1_pre_topc(B_548,A_549)
      | ~ l1_pre_topc(A_549)
      | ~ v2_pre_topc(A_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8177,plain,(
    ! [B_597,A_598] :
      ( v1_tsep_1(B_597,A_598)
      | ~ v3_pre_topc(u1_struct_0(B_597),A_598)
      | ~ v2_pre_topc(A_598)
      | ~ m1_pre_topc(B_597,A_598)
      | ~ l1_pre_topc(A_598) ) ),
    inference(resolution,[status(thm)],[c_34,c_7103])).

tff(c_8434,plain,(
    ! [A_604] :
      ( v1_tsep_1('#skF_3',A_604)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_604)
      | ~ v2_pre_topc(A_604)
      | ~ m1_pre_topc('#skF_3',A_604)
      | ~ l1_pre_topc(A_604) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_8177])).

tff(c_8438,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_8434])).

tff(c_8441,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_136,c_6935,c_8438])).

tff(c_397,plain,(
    ! [B_329,A_330] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_329),u1_pre_topc(B_329)),A_330)
      | ~ m1_pre_topc(B_329,A_330)
      | ~ l1_pre_topc(A_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_411,plain,(
    ! [A_330] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_330)
      | ~ m1_pre_topc('#skF_3',A_330)
      | ~ l1_pre_topc(A_330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_397])).

tff(c_426,plain,(
    ! [A_331] :
      ( m1_pre_topc('#skF_4',A_331)
      | ~ m1_pre_topc('#skF_3',A_331)
      | ~ l1_pre_topc(A_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_411])).

tff(c_430,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_426])).

tff(c_436,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_430])).

tff(c_7523,plain,(
    ! [B_570,A_571] :
      ( r1_tarski(u1_struct_0(B_570),u1_struct_0(A_571))
      | ~ m1_pre_topc(B_570,A_571)
      | ~ v2_pre_topc(A_571)
      | ~ l1_pre_topc(A_571) ) ),
    inference(resolution,[status(thm)],[c_36,c_557])).

tff(c_32,plain,(
    ! [B_41,C_43,A_37] :
      ( v1_tsep_1(B_41,C_43)
      | ~ r1_tarski(u1_struct_0(B_41),u1_struct_0(C_43))
      | ~ m1_pre_topc(C_43,A_37)
      | v2_struct_0(C_43)
      | ~ m1_pre_topc(B_41,A_37)
      | ~ v1_tsep_1(B_41,A_37)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_15822,plain,(
    ! [B_794,A_795,A_796] :
      ( v1_tsep_1(B_794,A_795)
      | ~ m1_pre_topc(A_795,A_796)
      | v2_struct_0(A_795)
      | ~ m1_pre_topc(B_794,A_796)
      | ~ v1_tsep_1(B_794,A_796)
      | ~ l1_pre_topc(A_796)
      | ~ v2_pre_topc(A_796)
      | v2_struct_0(A_796)
      | ~ m1_pre_topc(B_794,A_795)
      | ~ v2_pre_topc(A_795)
      | ~ l1_pre_topc(A_795) ) ),
    inference(resolution,[status(thm)],[c_7523,c_32])).

tff(c_15910,plain,(
    ! [B_794] :
      ( v1_tsep_1(B_794,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_794,'#skF_3')
      | ~ v1_tsep_1(B_794,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_794,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_436,c_15822])).

tff(c_16090,plain,(
    ! [B_794] :
      ( v1_tsep_1(B_794,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_794,'#skF_3')
      | ~ v1_tsep_1(B_794,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_794,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_177,c_180,c_136,c_15910])).

tff(c_16110,plain,(
    ! [B_799] :
      ( v1_tsep_1(B_799,'#skF_4')
      | ~ m1_pre_topc(B_799,'#skF_3')
      | ~ v1_tsep_1(B_799,'#skF_3')
      | ~ m1_pre_topc(B_799,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_68,c_16090])).

tff(c_16116,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_8441,c_16110])).

tff(c_16120,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_6935,c_16116])).

tff(c_16122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8122,c_16120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:04:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.99/4.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.11  
% 11.12/4.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.12  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.12/4.12  
% 11.12/4.12  %Foreground sorts:
% 11.12/4.12  
% 11.12/4.12  
% 11.12/4.12  %Background operators:
% 11.12/4.12  
% 11.12/4.12  
% 11.12/4.12  %Foreground operators:
% 11.12/4.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.12/4.12  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 11.12/4.12  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 11.12/4.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.12/4.12  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.12/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.12/4.12  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 11.12/4.12  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 11.12/4.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.12/4.12  tff('#skF_7', type, '#skF_7': $i).
% 11.12/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.12/4.12  tff('#skF_5', type, '#skF_5': $i).
% 11.12/4.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.12/4.12  tff('#skF_6', type, '#skF_6': $i).
% 11.12/4.12  tff('#skF_2', type, '#skF_2': $i).
% 11.12/4.12  tff('#skF_3', type, '#skF_3': $i).
% 11.12/4.12  tff('#skF_1', type, '#skF_1': $i).
% 11.12/4.12  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.12/4.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.12/4.12  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.12/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.12/4.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.12/4.12  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 11.12/4.12  tff('#skF_4', type, '#skF_4': $i).
% 11.12/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.12/4.12  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.12/4.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.12/4.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.12/4.12  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.12/4.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.12/4.12  
% 11.12/4.14  tff(f_277, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 11.12/4.14  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.12/4.14  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.12/4.14  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 11.12/4.14  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 11.12/4.14  tff(f_152, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 11.12/4.14  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 11.12/4.14  tff(f_166, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 11.12/4.14  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 11.12/4.14  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 11.12/4.14  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 11.12/4.14  tff(f_228, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 11.12/4.14  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 11.12/4.14  tff(f_117, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 11.12/4.14  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 11.12/4.14  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 11.12/4.14  tff(c_84, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_48, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_82, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_120, plain, (![B_313, A_314]: (l1_pre_topc(B_313) | ~m1_pre_topc(B_313, A_314) | ~l1_pre_topc(A_314))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.12/4.14  tff(c_126, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_120])).
% 11.12/4.14  tff(c_133, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_126])).
% 11.12/4.14  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.12/4.14  tff(c_93, plain, (![A_311]: (u1_struct_0(A_311)=k2_struct_0(A_311) | ~l1_struct_0(A_311))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.12/4.14  tff(c_97, plain, (![A_6]: (u1_struct_0(A_6)=k2_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_93])).
% 11.12/4.14  tff(c_141, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_133, c_97])).
% 11.12/4.14  tff(c_102, plain, (![A_312]: (u1_struct_0(A_312)=k2_struct_0(A_312) | ~l1_pre_topc(A_312))), inference(resolution, [status(thm)], [c_8, c_93])).
% 11.12/4.14  tff(c_110, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_102])).
% 11.12/4.14  tff(c_62, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_115, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_62])).
% 11.12/4.14  tff(c_147, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_115])).
% 11.12/4.14  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_137, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_60])).
% 11.12/4.14  tff(c_146, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_137])).
% 11.12/4.14  tff(c_129, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_120])).
% 11.12/4.14  tff(c_136, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_129])).
% 11.12/4.14  tff(c_145, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_136, c_97])).
% 11.12/4.14  tff(c_164, plain, (![B_316, A_317]: (v2_pre_topc(B_316) | ~m1_pre_topc(B_316, A_317) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_40])).
% 11.12/4.14  tff(c_170, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_164])).
% 11.12/4.14  tff(c_177, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_170])).
% 11.12/4.14  tff(c_36, plain, (![A_47]: (m1_pre_topc(A_47, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_152])).
% 11.12/4.14  tff(c_310, plain, (![B_324, A_325]: (m1_subset_1(u1_struct_0(B_324), k1_zfmisc_1(u1_struct_0(A_325))) | ~m1_pre_topc(B_324, A_325) | ~l1_pre_topc(A_325))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.12/4.14  tff(c_322, plain, (![B_324]: (m1_subset_1(u1_struct_0(B_324), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_324, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_141, c_310])).
% 11.12/4.14  tff(c_457, plain, (![B_332]: (m1_subset_1(u1_struct_0(B_332), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_332, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_322])).
% 11.12/4.14  tff(c_463, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_141, c_457])).
% 11.12/4.14  tff(c_527, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_463])).
% 11.12/4.14  tff(c_530, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_527])).
% 11.12/4.14  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_530])).
% 11.12/4.14  tff(c_536, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_463])).
% 11.12/4.14  tff(c_557, plain, (![B_338, C_339, A_340]: (r1_tarski(u1_struct_0(B_338), u1_struct_0(C_339)) | ~m1_pre_topc(B_338, C_339) | ~m1_pre_topc(C_339, A_340) | ~m1_pre_topc(B_338, A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.12/4.14  tff(c_559, plain, (![B_338]: (r1_tarski(u1_struct_0(B_338), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_338, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_536, c_557])).
% 11.12/4.14  tff(c_588, plain, (![B_341]: (r1_tarski(u1_struct_0(B_341), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_341, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_133, c_141, c_559])).
% 11.12/4.14  tff(c_591, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_145, c_588])).
% 11.12/4.14  tff(c_603, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_591])).
% 11.12/4.14  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_153, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_58])).
% 11.12/4.14  tff(c_181, plain, (![A_318]: (g1_pre_topc(u1_struct_0(A_318), u1_pre_topc(A_318))=A_318 | ~v1_pre_topc(A_318) | ~l1_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.12/4.14  tff(c_193, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_141, c_181])).
% 11.12/4.14  tff(c_205, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_193])).
% 11.12/4.14  tff(c_211, plain, (~v1_pre_topc('#skF_4')), inference(splitLeft, [status(thm)], [c_205])).
% 11.12/4.14  tff(c_212, plain, (![A_319]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_319), u1_pre_topc(A_319))) | ~l1_pre_topc(A_319) | v2_struct_0(A_319))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.12/4.14  tff(c_218, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_212])).
% 11.12/4.14  tff(c_229, plain, (v1_pre_topc('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_153, c_218])).
% 11.12/4.14  tff(c_231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_211, c_229])).
% 11.12/4.14  tff(c_232, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_205])).
% 11.12/4.14  tff(c_1180, plain, (![D_371, B_372, C_373, A_374]: (m1_pre_topc(D_371, B_372) | ~m1_pre_topc(C_373, A_374) | g1_pre_topc(u1_struct_0(D_371), u1_pre_topc(D_371))!=g1_pre_topc(u1_struct_0(C_373), u1_pre_topc(C_373)) | g1_pre_topc(u1_struct_0(B_372), u1_pre_topc(B_372))!=g1_pre_topc(u1_struct_0(A_374), u1_pre_topc(A_374)) | ~l1_pre_topc(D_371) | ~l1_pre_topc(C_373) | ~l1_pre_topc(B_372) | ~l1_pre_topc(A_374))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.12/4.14  tff(c_1225, plain, (![D_371, B_372, A_47]: (m1_pre_topc(D_371, B_372) | g1_pre_topc(u1_struct_0(D_371), u1_pre_topc(D_371))!=g1_pre_topc(u1_struct_0(A_47), u1_pre_topc(A_47)) | g1_pre_topc(u1_struct_0(B_372), u1_pre_topc(B_372))!=g1_pre_topc(u1_struct_0(A_47), u1_pre_topc(A_47)) | ~l1_pre_topc(D_371) | ~l1_pre_topc(B_372) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_36, c_1180])).
% 11.12/4.14  tff(c_6522, plain, (![A_529, B_530]: (m1_pre_topc(A_529, B_530) | g1_pre_topc(u1_struct_0(B_530), u1_pre_topc(B_530))!=g1_pre_topc(u1_struct_0(A_529), u1_pre_topc(A_529)) | ~l1_pre_topc(A_529) | ~l1_pre_topc(B_530) | ~l1_pre_topc(A_529))), inference(reflexivity, [status(thm), theory('equality')], [c_1225])).
% 11.12/4.14  tff(c_6560, plain, (![A_529]: (m1_pre_topc(A_529, '#skF_4') | g1_pre_topc(u1_struct_0(A_529), u1_pre_topc(A_529))!=g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc(A_529) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_529))), inference(superposition, [status(thm), theory('equality')], [c_141, c_6522])).
% 11.12/4.14  tff(c_6833, plain, (![A_539]: (m1_pre_topc(A_539, '#skF_4') | g1_pre_topc(u1_struct_0(A_539), u1_pre_topc(A_539))!='#skF_4' | ~l1_pre_topc(A_539))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_232, c_6560])).
% 11.12/4.14  tff(c_6860, plain, (m1_pre_topc('#skF_3', '#skF_4') | g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_4' | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_6833])).
% 11.12/4.14  tff(c_6875, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_153, c_6860])).
% 11.12/4.14  tff(c_6877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_603, c_6875])).
% 11.12/4.14  tff(c_6879, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_591])).
% 11.12/4.14  tff(c_56, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_148, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_56])).
% 11.12/4.14  tff(c_52, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_54, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_85, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54])).
% 11.12/4.14  tff(c_154, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_85])).
% 11.12/4.14  tff(c_50, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_277])).
% 11.12/4.14  tff(c_86, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50])).
% 11.12/4.14  tff(c_8116, plain, (![G_592, E_590, B_593, D_588, A_591, C_589]: (r1_tmap_1(D_588, B_593, E_590, G_592) | ~r1_tmap_1(C_589, B_593, k3_tmap_1(A_591, B_593, D_588, C_589, E_590), G_592) | ~m1_subset_1(G_592, u1_struct_0(C_589)) | ~m1_subset_1(G_592, u1_struct_0(D_588)) | ~m1_pre_topc(C_589, D_588) | ~v1_tsep_1(C_589, D_588) | ~m1_subset_1(E_590, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_588), u1_struct_0(B_593)))) | ~v1_funct_2(E_590, u1_struct_0(D_588), u1_struct_0(B_593)) | ~v1_funct_1(E_590) | ~m1_pre_topc(D_588, A_591) | v2_struct_0(D_588) | ~m1_pre_topc(C_589, A_591) | v2_struct_0(C_589) | ~l1_pre_topc(B_593) | ~v2_pre_topc(B_593) | v2_struct_0(B_593) | ~l1_pre_topc(A_591) | ~v2_pre_topc(A_591) | v2_struct_0(A_591))), inference(cnfTransformation, [status(thm)], [f_228])).
% 11.12/4.14  tff(c_8118, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_8116])).
% 11.12/4.14  tff(c_8121, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_70, c_66, c_64, c_147, c_110, c_141, c_146, c_110, c_141, c_6879, c_148, c_141, c_154, c_145, c_8118])).
% 11.12/4.14  tff(c_8122, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_72, c_68, c_48, c_8121])).
% 11.12/4.14  tff(c_316, plain, (![B_324]: (m1_subset_1(u1_struct_0(B_324), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_324, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_310])).
% 11.12/4.14  tff(c_471, plain, (![B_333]: (m1_subset_1(u1_struct_0(B_333), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_333, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_316])).
% 11.12/4.14  tff(c_474, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_471])).
% 11.12/4.14  tff(c_6920, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_474])).
% 11.12/4.14  tff(c_6926, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_6920])).
% 11.12/4.14  tff(c_6933, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_6926])).
% 11.12/4.14  tff(c_6935, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_474])).
% 11.12/4.14  tff(c_173, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_164])).
% 11.12/4.14  tff(c_180, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_173])).
% 11.12/4.14  tff(c_18, plain, (![A_26]: (v3_pre_topc(k2_struct_0(A_26), A_26) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.12/4.14  tff(c_34, plain, (![B_46, A_44]: (m1_subset_1(u1_struct_0(B_46), k1_zfmisc_1(u1_struct_0(A_44))) | ~m1_pre_topc(B_46, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.12/4.14  tff(c_7103, plain, (![B_548, A_549]: (v1_tsep_1(B_548, A_549) | ~v3_pre_topc(u1_struct_0(B_548), A_549) | ~m1_subset_1(u1_struct_0(B_548), k1_zfmisc_1(u1_struct_0(A_549))) | ~m1_pre_topc(B_548, A_549) | ~l1_pre_topc(A_549) | ~v2_pre_topc(A_549))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.12/4.14  tff(c_8177, plain, (![B_597, A_598]: (v1_tsep_1(B_597, A_598) | ~v3_pre_topc(u1_struct_0(B_597), A_598) | ~v2_pre_topc(A_598) | ~m1_pre_topc(B_597, A_598) | ~l1_pre_topc(A_598))), inference(resolution, [status(thm)], [c_34, c_7103])).
% 11.12/4.14  tff(c_8434, plain, (![A_604]: (v1_tsep_1('#skF_3', A_604) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_604) | ~v2_pre_topc(A_604) | ~m1_pre_topc('#skF_3', A_604) | ~l1_pre_topc(A_604))), inference(superposition, [status(thm), theory('equality')], [c_145, c_8177])).
% 11.12/4.14  tff(c_8438, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_8434])).
% 11.12/4.14  tff(c_8441, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_180, c_136, c_6935, c_8438])).
% 11.12/4.14  tff(c_397, plain, (![B_329, A_330]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_329), u1_pre_topc(B_329)), A_330) | ~m1_pre_topc(B_329, A_330) | ~l1_pre_topc(A_330))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.12/4.14  tff(c_411, plain, (![A_330]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_330) | ~m1_pre_topc('#skF_3', A_330) | ~l1_pre_topc(A_330))), inference(superposition, [status(thm), theory('equality')], [c_145, c_397])).
% 11.12/4.14  tff(c_426, plain, (![A_331]: (m1_pre_topc('#skF_4', A_331) | ~m1_pre_topc('#skF_3', A_331) | ~l1_pre_topc(A_331))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_411])).
% 11.12/4.14  tff(c_430, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_426])).
% 11.12/4.14  tff(c_436, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_430])).
% 11.12/4.14  tff(c_7523, plain, (![B_570, A_571]: (r1_tarski(u1_struct_0(B_570), u1_struct_0(A_571)) | ~m1_pre_topc(B_570, A_571) | ~v2_pre_topc(A_571) | ~l1_pre_topc(A_571))), inference(resolution, [status(thm)], [c_36, c_557])).
% 11.12/4.14  tff(c_32, plain, (![B_41, C_43, A_37]: (v1_tsep_1(B_41, C_43) | ~r1_tarski(u1_struct_0(B_41), u1_struct_0(C_43)) | ~m1_pre_topc(C_43, A_37) | v2_struct_0(C_43) | ~m1_pre_topc(B_41, A_37) | ~v1_tsep_1(B_41, A_37) | ~l1_pre_topc(A_37) | ~v2_pre_topc(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_141])).
% 11.12/4.14  tff(c_15822, plain, (![B_794, A_795, A_796]: (v1_tsep_1(B_794, A_795) | ~m1_pre_topc(A_795, A_796) | v2_struct_0(A_795) | ~m1_pre_topc(B_794, A_796) | ~v1_tsep_1(B_794, A_796) | ~l1_pre_topc(A_796) | ~v2_pre_topc(A_796) | v2_struct_0(A_796) | ~m1_pre_topc(B_794, A_795) | ~v2_pre_topc(A_795) | ~l1_pre_topc(A_795))), inference(resolution, [status(thm)], [c_7523, c_32])).
% 11.12/4.14  tff(c_15910, plain, (![B_794]: (v1_tsep_1(B_794, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_794, '#skF_3') | ~v1_tsep_1(B_794, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_794, '#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_436, c_15822])).
% 11.12/4.14  tff(c_16090, plain, (![B_794]: (v1_tsep_1(B_794, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_794, '#skF_3') | ~v1_tsep_1(B_794, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_794, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_177, c_180, c_136, c_15910])).
% 11.12/4.14  tff(c_16110, plain, (![B_799]: (v1_tsep_1(B_799, '#skF_4') | ~m1_pre_topc(B_799, '#skF_3') | ~v1_tsep_1(B_799, '#skF_3') | ~m1_pre_topc(B_799, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_68, c_16090])).
% 11.12/4.14  tff(c_16116, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_8441, c_16110])).
% 11.12/4.14  tff(c_16120, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6879, c_6935, c_16116])).
% 11.12/4.14  tff(c_16122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8122, c_16120])).
% 11.12/4.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.12/4.14  
% 11.12/4.14  Inference rules
% 11.12/4.14  ----------------------
% 11.12/4.14  #Ref     : 12
% 11.12/4.14  #Sup     : 3691
% 11.12/4.14  #Fact    : 0
% 11.12/4.14  #Define  : 0
% 11.12/4.14  #Split   : 30
% 11.12/4.14  #Chain   : 0
% 11.12/4.14  #Close   : 0
% 11.12/4.14  
% 11.12/4.14  Ordering : KBO
% 11.12/4.14  
% 11.12/4.14  Simplification rules
% 11.12/4.14  ----------------------
% 11.12/4.14  #Subsume      : 704
% 11.12/4.14  #Demod        : 5384
% 11.12/4.14  #Tautology    : 721
% 11.12/4.14  #SimpNegUnit  : 213
% 11.12/4.14  #BackRed      : 6
% 11.12/4.14  
% 11.12/4.14  #Partial instantiations: 0
% 11.12/4.14  #Strategies tried      : 1
% 11.12/4.14  
% 11.12/4.14  Timing (in seconds)
% 11.12/4.14  ----------------------
% 11.12/4.14  Preprocessing        : 0.42
% 11.12/4.14  Parsing              : 0.22
% 11.12/4.14  CNF conversion       : 0.05
% 11.12/4.14  Main loop            : 2.93
% 11.12/4.14  Inferencing          : 0.71
% 11.12/4.14  Reduction            : 1.27
% 11.12/4.14  Demodulation         : 0.99
% 11.12/4.15  BG Simplification    : 0.09
% 11.12/4.15  Subsumption          : 0.70
% 11.12/4.15  Abstraction          : 0.11
% 11.12/4.15  MUC search           : 0.00
% 11.12/4.15  Cooper               : 0.00
% 11.12/4.15  Total                : 3.40
% 11.12/4.15  Index Insertion      : 0.00
% 11.12/4.15  Index Deletion       : 0.00
% 11.12/4.15  Index Matching       : 0.00
% 11.12/4.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
