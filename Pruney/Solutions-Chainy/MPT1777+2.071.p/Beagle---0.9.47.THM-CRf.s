%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:42 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.02s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 715 expanded)
%              Number of leaves         :   44 ( 267 expanded)
%              Depth                    :   14
%              Number of atoms          :  312 (3351 expanded)
%              Number of equality atoms :   14 ( 362 expanded)
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

tff(f_244,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_126,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_195,axiom,(
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

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_91,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_115,axiom,(
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

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_115,plain,(
    ! [B_295,A_296] :
      ( l1_pre_topc(B_295)
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_115])).

tff(c_131,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_124])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_293] :
      ( u1_struct_0(A_293) = k2_struct_0(A_293)
      | ~ l1_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_139,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_95])).

tff(c_96,plain,(
    ! [A_294] :
      ( u1_struct_0(A_294) = k2_struct_0(A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_104,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_96])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_110,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56])).

tff(c_150,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_110])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_109,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_54])).

tff(c_174,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_109])).

tff(c_121,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_128,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_121])).

tff(c_135,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_95])).

tff(c_175,plain,(
    ! [B_300,A_301] :
      ( r1_tarski(u1_struct_0(B_300),u1_struct_0(A_301))
      | ~ m1_pre_topc(B_300,A_301)
      | ~ l1_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_181,plain,(
    ! [B_300] :
      ( r1_tarski(u1_struct_0(B_300),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_300,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_175])).

tff(c_208,plain,(
    ! [B_302] :
      ( r1_tarski(u1_struct_0(B_302),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_302,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_181])).

tff(c_214,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_208])).

tff(c_514,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_32,plain,(
    ! [A_33] :
      ( m1_pre_topc(A_33,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_187,plain,(
    ! [B_300] :
      ( r1_tarski(u1_struct_0(B_300),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_300,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_175])).

tff(c_221,plain,(
    ! [B_303] :
      ( r1_tarski(u1_struct_0(B_303),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_303,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_187])).

tff(c_227,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_221])).

tff(c_469,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_472,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_469])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_472])).

tff(c_478,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_140,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_52])).

tff(c_693,plain,(
    ! [A_323,B_324] :
      ( m1_pre_topc(A_323,g1_pre_topc(u1_struct_0(B_324),u1_pre_topc(B_324)))
      | ~ m1_pre_topc(A_323,B_324)
      | ~ l1_pre_topc(B_324)
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_720,plain,(
    ! [A_323] :
      ( m1_pre_topc(A_323,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_323,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_693])).

tff(c_746,plain,(
    ! [A_325] :
      ( m1_pre_topc(A_325,'#skF_4')
      | ~ m1_pre_topc(A_325,'#skF_3')
      | ~ l1_pre_topc(A_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_140,c_720])).

tff(c_752,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_478,c_746])).

tff(c_767,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_752])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_767])).

tff(c_771,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_151,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_50])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_79,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_141,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_79])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_2215,plain,(
    ! [B_372,A_374,D_377,C_376,G_375,E_373] :
      ( r1_tmap_1(D_377,B_372,E_373,G_375)
      | ~ r1_tmap_1(C_376,B_372,k3_tmap_1(A_374,B_372,D_377,C_376,E_373),G_375)
      | ~ m1_subset_1(G_375,u1_struct_0(C_376))
      | ~ m1_subset_1(G_375,u1_struct_0(D_377))
      | ~ m1_pre_topc(C_376,D_377)
      | ~ v1_tsep_1(C_376,D_377)
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_377),u1_struct_0(B_372))))
      | ~ v1_funct_2(E_373,u1_struct_0(D_377),u1_struct_0(B_372))
      | ~ v1_funct_1(E_373)
      | ~ m1_pre_topc(D_377,A_374)
      | v2_struct_0(D_377)
      | ~ m1_pre_topc(C_376,A_374)
      | v2_struct_0(C_376)
      | ~ l1_pre_topc(B_372)
      | ~ v2_pre_topc(B_372)
      | v2_struct_0(B_372)
      | ~ l1_pre_topc(A_374)
      | ~ v2_pre_topc(A_374)
      | v2_struct_0(A_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2217,plain,
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
    inference(resolution,[status(thm)],[c_80,c_2215])).

tff(c_2220,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_150,c_104,c_139,c_174,c_104,c_139,c_771,c_151,c_139,c_141,c_135,c_2217])).

tff(c_2221,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_42,c_2220])).

tff(c_157,plain,(
    ! [B_298,A_299] :
      ( v2_pre_topc(B_298)
      | ~ m1_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_163,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_157])).

tff(c_170,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_163])).

tff(c_14,plain,(
    ! [A_12] :
      ( v3_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(u1_struct_0(B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1406,plain,(
    ! [B_348,A_349] :
      ( v1_tsep_1(B_348,A_349)
      | ~ v3_pre_topc(u1_struct_0(B_348),A_349)
      | ~ m1_subset_1(u1_struct_0(B_348),k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ m1_pre_topc(B_348,A_349)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3170,plain,(
    ! [B_399,A_400] :
      ( v1_tsep_1(B_399,A_400)
      | ~ v3_pre_topc(u1_struct_0(B_399),A_400)
      | ~ v2_pre_topc(A_400)
      | ~ m1_pre_topc(B_399,A_400)
      | ~ l1_pre_topc(A_400) ) ),
    inference(resolution,[status(thm)],[c_30,c_1406])).

tff(c_3433,plain,(
    ! [A_415] :
      ( v1_tsep_1('#skF_3',A_415)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_415)
      | ~ v2_pre_topc(A_415)
      | ~ m1_pre_topc('#skF_3',A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_3170])).

tff(c_3440,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3433])).

tff(c_3444,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_128,c_478,c_3440])).

tff(c_363,plain,(
    ! [B_311,A_312] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_311),u1_pre_topc(B_311)),A_312)
      | ~ m1_pre_topc(B_311,A_312)
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_377,plain,(
    ! [A_312] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_312)
      | ~ m1_pre_topc('#skF_3',A_312)
      | ~ l1_pre_topc(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_363])).

tff(c_388,plain,(
    ! [A_313] :
      ( m1_pre_topc('#skF_4',A_313)
      | ~ m1_pre_topc('#skF_3',A_313)
      | ~ l1_pre_topc(A_313) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_377])).

tff(c_392,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_388])).

tff(c_398,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_392])).

tff(c_34,plain,(
    ! [B_36,A_34] :
      ( r1_tarski(u1_struct_0(B_36),u1_struct_0(A_34))
      | ~ m1_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1830,plain,(
    ! [B_363,C_364,A_365] :
      ( v1_tsep_1(B_363,C_364)
      | ~ r1_tarski(u1_struct_0(B_363),u1_struct_0(C_364))
      | ~ m1_pre_topc(C_364,A_365)
      | v2_struct_0(C_364)
      | ~ m1_pre_topc(B_363,A_365)
      | ~ v1_tsep_1(B_363,A_365)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5978,plain,(
    ! [B_469,A_470,A_471] :
      ( v1_tsep_1(B_469,A_470)
      | ~ m1_pre_topc(A_470,A_471)
      | v2_struct_0(A_470)
      | ~ m1_pre_topc(B_469,A_471)
      | ~ v1_tsep_1(B_469,A_471)
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | v2_struct_0(A_471)
      | ~ m1_pre_topc(B_469,A_470)
      | ~ l1_pre_topc(A_470) ) ),
    inference(resolution,[status(thm)],[c_34,c_1830])).

tff(c_6042,plain,(
    ! [B_469] :
      ( v1_tsep_1(B_469,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_469,'#skF_3')
      | ~ v1_tsep_1(B_469,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_469,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_398,c_5978])).

tff(c_6167,plain,(
    ! [B_469] :
      ( v1_tsep_1(B_469,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_469,'#skF_3')
      | ~ v1_tsep_1(B_469,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_469,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_170,c_128,c_6042])).

tff(c_6192,plain,(
    ! [B_475] :
      ( v1_tsep_1(B_475,'#skF_4')
      | ~ m1_pre_topc(B_475,'#skF_3')
      | ~ v1_tsep_1(B_475,'#skF_3')
      | ~ m1_pre_topc(B_475,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_62,c_6167])).

tff(c_6201,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_3444,c_6192])).

tff(c_6206,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_478,c_6201])).

tff(c_6208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2221,c_6206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:00:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.40  
% 7.02/2.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.40  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.02/2.40  
% 7.02/2.40  %Foreground sorts:
% 7.02/2.40  
% 7.02/2.40  
% 7.02/2.40  %Background operators:
% 7.02/2.40  
% 7.02/2.40  
% 7.02/2.40  %Foreground operators:
% 7.02/2.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.02/2.40  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.02/2.40  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.02/2.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.02/2.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.02/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.02/2.40  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.02/2.40  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.02/2.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.02/2.40  tff('#skF_7', type, '#skF_7': $i).
% 7.02/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.02/2.40  tff('#skF_5', type, '#skF_5': $i).
% 7.02/2.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.02/2.40  tff('#skF_6', type, '#skF_6': $i).
% 7.02/2.40  tff('#skF_2', type, '#skF_2': $i).
% 7.02/2.40  tff('#skF_3', type, '#skF_3': $i).
% 7.02/2.40  tff('#skF_1', type, '#skF_1': $i).
% 7.02/2.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.02/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.02/2.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.02/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.02/2.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.02/2.40  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 7.02/2.40  tff('#skF_4', type, '#skF_4': $i).
% 7.02/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.02/2.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.02/2.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.02/2.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.02/2.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.02/2.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.02/2.40  
% 7.02/2.43  tff(f_244, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 7.02/2.43  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.02/2.43  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.02/2.43  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.02/2.43  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 7.02/2.43  tff(f_126, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.02/2.43  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 7.02/2.43  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 7.02/2.43  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.02/2.43  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 7.02/2.43  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.02/2.43  tff(f_91, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 7.02/2.43  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 7.02/2.43  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 7.02/2.43  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_115, plain, (![B_295, A_296]: (l1_pre_topc(B_295) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.02/2.43  tff(c_124, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_115])).
% 7.02/2.43  tff(c_131, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_124])).
% 7.02/2.43  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.02/2.43  tff(c_91, plain, (![A_293]: (u1_struct_0(A_293)=k2_struct_0(A_293) | ~l1_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.02/2.43  tff(c_95, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_91])).
% 7.02/2.43  tff(c_139, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_131, c_95])).
% 7.02/2.43  tff(c_96, plain, (![A_294]: (u1_struct_0(A_294)=k2_struct_0(A_294) | ~l1_pre_topc(A_294))), inference(resolution, [status(thm)], [c_6, c_91])).
% 7.02/2.43  tff(c_104, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_96])).
% 7.02/2.43  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_110, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56])).
% 7.02/2.43  tff(c_150, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_110])).
% 7.02/2.43  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_109, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_54])).
% 7.02/2.43  tff(c_174, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_109])).
% 7.02/2.43  tff(c_121, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_115])).
% 7.02/2.43  tff(c_128, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_121])).
% 7.02/2.43  tff(c_135, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_128, c_95])).
% 7.02/2.43  tff(c_175, plain, (![B_300, A_301]: (r1_tarski(u1_struct_0(B_300), u1_struct_0(A_301)) | ~m1_pre_topc(B_300, A_301) | ~l1_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.02/2.43  tff(c_181, plain, (![B_300]: (r1_tarski(u1_struct_0(B_300), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_300, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_175])).
% 7.02/2.43  tff(c_208, plain, (![B_302]: (r1_tarski(u1_struct_0(B_302), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_302, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_181])).
% 7.02/2.43  tff(c_214, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_208])).
% 7.02/2.43  tff(c_514, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_214])).
% 7.02/2.43  tff(c_32, plain, (![A_33]: (m1_pre_topc(A_33, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.02/2.43  tff(c_187, plain, (![B_300]: (r1_tarski(u1_struct_0(B_300), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_300, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_175])).
% 7.02/2.43  tff(c_221, plain, (![B_303]: (r1_tarski(u1_struct_0(B_303), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_303, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_187])).
% 7.02/2.43  tff(c_227, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_135, c_221])).
% 7.02/2.43  tff(c_469, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_227])).
% 7.02/2.43  tff(c_472, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_469])).
% 7.02/2.43  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_472])).
% 7.02/2.43  tff(c_478, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_227])).
% 7.02/2.43  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_140, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_52])).
% 7.02/2.43  tff(c_693, plain, (![A_323, B_324]: (m1_pre_topc(A_323, g1_pre_topc(u1_struct_0(B_324), u1_pre_topc(B_324))) | ~m1_pre_topc(A_323, B_324) | ~l1_pre_topc(B_324) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.02/2.43  tff(c_720, plain, (![A_323]: (m1_pre_topc(A_323, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_323, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_323))), inference(superposition, [status(thm), theory('equality')], [c_135, c_693])).
% 7.02/2.43  tff(c_746, plain, (![A_325]: (m1_pre_topc(A_325, '#skF_4') | ~m1_pre_topc(A_325, '#skF_3') | ~l1_pre_topc(A_325))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_140, c_720])).
% 7.02/2.43  tff(c_752, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_478, c_746])).
% 7.02/2.43  tff(c_767, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_752])).
% 7.02/2.43  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_767])).
% 7.02/2.43  tff(c_771, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_214])).
% 7.02/2.43  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_151, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_50])).
% 7.02/2.43  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_79, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 7.02/2.43  tff(c_141, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_79])).
% 7.02/2.43  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_244])).
% 7.02/2.43  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 7.02/2.43  tff(c_2215, plain, (![B_372, A_374, D_377, C_376, G_375, E_373]: (r1_tmap_1(D_377, B_372, E_373, G_375) | ~r1_tmap_1(C_376, B_372, k3_tmap_1(A_374, B_372, D_377, C_376, E_373), G_375) | ~m1_subset_1(G_375, u1_struct_0(C_376)) | ~m1_subset_1(G_375, u1_struct_0(D_377)) | ~m1_pre_topc(C_376, D_377) | ~v1_tsep_1(C_376, D_377) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_377), u1_struct_0(B_372)))) | ~v1_funct_2(E_373, u1_struct_0(D_377), u1_struct_0(B_372)) | ~v1_funct_1(E_373) | ~m1_pre_topc(D_377, A_374) | v2_struct_0(D_377) | ~m1_pre_topc(C_376, A_374) | v2_struct_0(C_376) | ~l1_pre_topc(B_372) | ~v2_pre_topc(B_372) | v2_struct_0(B_372) | ~l1_pre_topc(A_374) | ~v2_pre_topc(A_374) | v2_struct_0(A_374))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.02/2.43  tff(c_2217, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_2215])).
% 7.02/2.43  tff(c_2220, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_150, c_104, c_139, c_174, c_104, c_139, c_771, c_151, c_139, c_141, c_135, c_2217])).
% 7.02/2.43  tff(c_2221, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_42, c_2220])).
% 7.02/2.43  tff(c_157, plain, (![B_298, A_299]: (v2_pre_topc(B_298) | ~m1_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.02/2.43  tff(c_163, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_157])).
% 7.02/2.43  tff(c_170, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_163])).
% 7.02/2.43  tff(c_14, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.02/2.43  tff(c_30, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.02/2.43  tff(c_1406, plain, (![B_348, A_349]: (v1_tsep_1(B_348, A_349) | ~v3_pre_topc(u1_struct_0(B_348), A_349) | ~m1_subset_1(u1_struct_0(B_348), k1_zfmisc_1(u1_struct_0(A_349))) | ~m1_pre_topc(B_348, A_349) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.02/2.43  tff(c_3170, plain, (![B_399, A_400]: (v1_tsep_1(B_399, A_400) | ~v3_pre_topc(u1_struct_0(B_399), A_400) | ~v2_pre_topc(A_400) | ~m1_pre_topc(B_399, A_400) | ~l1_pre_topc(A_400))), inference(resolution, [status(thm)], [c_30, c_1406])).
% 7.02/2.43  tff(c_3433, plain, (![A_415]: (v1_tsep_1('#skF_3', A_415) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_415) | ~v2_pre_topc(A_415) | ~m1_pre_topc('#skF_3', A_415) | ~l1_pre_topc(A_415))), inference(superposition, [status(thm), theory('equality')], [c_135, c_3170])).
% 7.02/2.43  tff(c_3440, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_3433])).
% 7.02/2.43  tff(c_3444, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_128, c_478, c_3440])).
% 7.02/2.43  tff(c_363, plain, (![B_311, A_312]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_311), u1_pre_topc(B_311)), A_312) | ~m1_pre_topc(B_311, A_312) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.02/2.43  tff(c_377, plain, (![A_312]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_312) | ~m1_pre_topc('#skF_3', A_312) | ~l1_pre_topc(A_312))), inference(superposition, [status(thm), theory('equality')], [c_135, c_363])).
% 7.02/2.43  tff(c_388, plain, (![A_313]: (m1_pre_topc('#skF_4', A_313) | ~m1_pre_topc('#skF_3', A_313) | ~l1_pre_topc(A_313))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_377])).
% 7.02/2.43  tff(c_392, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_388])).
% 7.02/2.43  tff(c_398, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_392])).
% 7.02/2.43  tff(c_34, plain, (![B_36, A_34]: (r1_tarski(u1_struct_0(B_36), u1_struct_0(A_34)) | ~m1_pre_topc(B_36, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.02/2.43  tff(c_1830, plain, (![B_363, C_364, A_365]: (v1_tsep_1(B_363, C_364) | ~r1_tarski(u1_struct_0(B_363), u1_struct_0(C_364)) | ~m1_pre_topc(C_364, A_365) | v2_struct_0(C_364) | ~m1_pre_topc(B_363, A_365) | ~v1_tsep_1(B_363, A_365) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.02/2.43  tff(c_5978, plain, (![B_469, A_470, A_471]: (v1_tsep_1(B_469, A_470) | ~m1_pre_topc(A_470, A_471) | v2_struct_0(A_470) | ~m1_pre_topc(B_469, A_471) | ~v1_tsep_1(B_469, A_471) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | v2_struct_0(A_471) | ~m1_pre_topc(B_469, A_470) | ~l1_pre_topc(A_470))), inference(resolution, [status(thm)], [c_34, c_1830])).
% 7.02/2.43  tff(c_6042, plain, (![B_469]: (v1_tsep_1(B_469, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_469, '#skF_3') | ~v1_tsep_1(B_469, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_469, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_398, c_5978])).
% 7.02/2.43  tff(c_6167, plain, (![B_469]: (v1_tsep_1(B_469, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_469, '#skF_3') | ~v1_tsep_1(B_469, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_469, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_170, c_128, c_6042])).
% 7.02/2.43  tff(c_6192, plain, (![B_475]: (v1_tsep_1(B_475, '#skF_4') | ~m1_pre_topc(B_475, '#skF_3') | ~v1_tsep_1(B_475, '#skF_3') | ~m1_pre_topc(B_475, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_62, c_6167])).
% 7.02/2.43  tff(c_6201, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_3444, c_6192])).
% 7.02/2.43  tff(c_6206, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_478, c_6201])).
% 7.02/2.43  tff(c_6208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2221, c_6206])).
% 7.02/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.02/2.43  
% 7.02/2.43  Inference rules
% 7.02/2.43  ----------------------
% 7.02/2.43  #Ref     : 0
% 7.02/2.43  #Sup     : 1321
% 7.02/2.43  #Fact    : 0
% 7.02/2.43  #Define  : 0
% 7.02/2.43  #Split   : 15
% 7.02/2.43  #Chain   : 0
% 7.02/2.43  #Close   : 0
% 7.02/2.43  
% 7.02/2.43  Ordering : KBO
% 7.02/2.43  
% 7.02/2.43  Simplification rules
% 7.02/2.43  ----------------------
% 7.02/2.43  #Subsume      : 232
% 7.02/2.43  #Demod        : 1843
% 7.02/2.43  #Tautology    : 343
% 7.02/2.43  #SimpNegUnit  : 67
% 7.02/2.43  #BackRed      : 6
% 7.02/2.43  
% 7.02/2.43  #Partial instantiations: 0
% 7.02/2.43  #Strategies tried      : 1
% 7.02/2.43  
% 7.02/2.43  Timing (in seconds)
% 7.02/2.43  ----------------------
% 7.02/2.43  Preprocessing        : 0.39
% 7.02/2.43  Parsing              : 0.20
% 7.02/2.43  CNF conversion       : 0.05
% 7.02/2.43  Main loop            : 1.26
% 7.02/2.43  Inferencing          : 0.34
% 7.02/2.43  Reduction            : 0.53
% 7.02/2.43  Demodulation         : 0.40
% 7.02/2.43  BG Simplification    : 0.04
% 7.02/2.43  Subsumption          : 0.25
% 7.02/2.43  Abstraction          : 0.04
% 7.02/2.43  MUC search           : 0.00
% 7.02/2.43  Cooper               : 0.00
% 7.02/2.43  Total                : 1.70
% 7.02/2.43  Index Insertion      : 0.00
% 7.02/2.43  Index Deletion       : 0.00
% 7.02/2.43  Index Matching       : 0.00
% 7.02/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
