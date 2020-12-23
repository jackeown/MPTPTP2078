%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:38 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 731 expanded)
%              Number of leaves         :   42 ( 270 expanded)
%              Depth                    :   15
%              Number of atoms          :  263 (3316 expanded)
%              Number of equality atoms :   19 ( 375 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_217,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_64,axiom,(
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

tff(f_168,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_88,axiom,(
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

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_114,plain,(
    ! [B_288,A_289] :
      ( l1_pre_topc(B_288)
      | ~ m1_pre_topc(B_288,A_289)
      | ~ l1_pre_topc(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_114])).

tff(c_130,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_123])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,(
    ! [A_286] :
      ( u1_struct_0(A_286) = k2_struct_0(A_286)
      | ~ l1_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_95,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_138,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_95])).

tff(c_96,plain,(
    ! [A_287] :
      ( u1_struct_0(A_287) = k2_struct_0(A_287)
      | ~ l1_pre_topc(A_287) ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_104,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_96])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_109,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_54])).

tff(c_147,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_109])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_145,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_52])).

tff(c_146,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_145])).

tff(c_120,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_114])).

tff(c_127,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_120])).

tff(c_134,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_95])).

tff(c_182,plain,(
    ! [B_295,A_296] :
      ( r1_tarski(u1_struct_0(B_295),u1_struct_0(A_296))
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_190,plain,(
    ! [B_295] :
      ( r1_tarski(u1_struct_0(B_295),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_295,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_182])).

tff(c_218,plain,(
    ! [B_297] :
      ( r1_tarski(u1_struct_0(B_297),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_297,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_190])).

tff(c_226,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_218])).

tff(c_478,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_30,plain,(
    ! [A_25] :
      ( m1_pre_topc(A_25,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_139,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_50])).

tff(c_603,plain,(
    ! [A_321,B_322] :
      ( m1_pre_topc(A_321,g1_pre_topc(u1_struct_0(B_322),u1_pre_topc(B_322)))
      | ~ m1_pre_topc(A_321,B_322)
      | ~ l1_pre_topc(B_322)
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_624,plain,(
    ! [A_321] :
      ( m1_pre_topc(A_321,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_321,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_603])).

tff(c_646,plain,(
    ! [A_323] :
      ( m1_pre_topc(A_323,'#skF_4')
      | ~ m1_pre_topc(A_323,'#skF_3')
      | ~ l1_pre_topc(A_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_139,c_624])).

tff(c_660,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_646])).

tff(c_671,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_660])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_671])).

tff(c_675,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_148,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_48])).

tff(c_354,plain,(
    ! [A_307,B_308] :
      ( m1_pre_topc(A_307,B_308)
      | ~ m1_pre_topc(A_307,g1_pre_topc(u1_struct_0(B_308),u1_pre_topc(B_308)))
      | ~ l1_pre_topc(B_308)
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_360,plain,(
    ! [A_307] :
      ( m1_pre_topc(A_307,'#skF_3')
      | ~ m1_pre_topc(A_307,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_354])).

tff(c_380,plain,(
    ! [A_309] :
      ( m1_pre_topc(A_309,'#skF_3')
      | ~ m1_pre_topc(A_309,'#skF_4')
      | ~ l1_pre_topc(A_309) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_139,c_360])).

tff(c_196,plain,(
    ! [B_295] :
      ( r1_tarski(u1_struct_0(B_295),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_295,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_182])).

tff(c_295,plain,(
    ! [B_301] :
      ( r1_tarski(u1_struct_0(B_301),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_301,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_196])).

tff(c_300,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_295])).

tff(c_330,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_300])).

tff(c_392,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_380,c_330])).

tff(c_409,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_392])).

tff(c_418,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_409])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_418])).

tff(c_423,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_300])).

tff(c_674,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_692,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_674,c_2])).

tff(c_695,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_692])).

tff(c_710,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_134])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_1533,plain,(
    ! [D_365,C_364,E_368,A_367,G_369,B_366] :
      ( r1_tmap_1(D_365,B_366,E_368,G_369)
      | ~ r1_tmap_1(C_364,B_366,k3_tmap_1(A_367,B_366,D_365,C_364,E_368),G_369)
      | ~ m1_subset_1(G_369,u1_struct_0(C_364))
      | ~ m1_subset_1(G_369,u1_struct_0(D_365))
      | ~ m1_pre_topc(C_364,D_365)
      | ~ v1_tsep_1(C_364,D_365)
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_365),u1_struct_0(B_366))))
      | ~ v1_funct_2(E_368,u1_struct_0(D_365),u1_struct_0(B_366))
      | ~ v1_funct_1(E_368)
      | ~ m1_pre_topc(D_365,A_367)
      | v2_struct_0(D_365)
      | ~ m1_pre_topc(C_364,A_367)
      | v2_struct_0(C_364)
      | ~ l1_pre_topc(B_366)
      | ~ v2_pre_topc(B_366)
      | v2_struct_0(B_366)
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367)
      | v2_struct_0(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_1535,plain,
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
    inference(resolution,[status(thm)],[c_78,c_1533])).

tff(c_1538,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_147,c_104,c_138,c_146,c_104,c_138,c_675,c_148,c_138,c_148,c_710,c_1535])).

tff(c_1539,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_40,c_1538])).

tff(c_165,plain,(
    ! [B_293,A_294] :
      ( v2_pre_topc(B_293)
      | ~ m1_pre_topc(B_293,A_294)
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_174,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_165])).

tff(c_181,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_174])).

tff(c_20,plain,(
    ! [A_14] :
      ( v3_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [B_24,A_22] :
      ( m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1072,plain,(
    ! [B_339,A_340] :
      ( v1_tsep_1(B_339,A_340)
      | ~ v3_pre_topc(u1_struct_0(B_339),A_340)
      | ~ m1_subset_1(u1_struct_0(B_339),k1_zfmisc_1(u1_struct_0(A_340)))
      | ~ m1_pre_topc(B_339,A_340)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1985,plain,(
    ! [B_400,A_401] :
      ( v1_tsep_1(B_400,A_401)
      | ~ v3_pre_topc(u1_struct_0(B_400),A_401)
      | ~ v2_pre_topc(A_401)
      | ~ m1_pre_topc(B_400,A_401)
      | ~ l1_pre_topc(A_401) ) ),
    inference(resolution,[status(thm)],[c_28,c_1072])).

tff(c_2486,plain,(
    ! [A_436] :
      ( v1_tsep_1('#skF_3',A_436)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_436)
      | ~ v2_pre_topc(A_436)
      | ~ m1_pre_topc('#skF_3',A_436)
      | ~ l1_pre_topc(A_436) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_1985])).

tff(c_2499,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_2486])).

tff(c_2507,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_130,c_675,c_2499])).

tff(c_2509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1539,c_2507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.86  
% 4.51/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.86  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.51/1.86  
% 4.51/1.86  %Foreground sorts:
% 4.51/1.86  
% 4.51/1.86  
% 4.51/1.86  %Background operators:
% 4.51/1.86  
% 4.51/1.86  
% 4.51/1.86  %Foreground operators:
% 4.51/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.51/1.86  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.51/1.86  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.51/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.51/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.86  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.51/1.86  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.51/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.51/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.51/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.51/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.86  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.51/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.86  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.51/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.51/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.51/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.51/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.86  
% 4.51/1.89  tff(f_217, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.51/1.89  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.51/1.89  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.51/1.89  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.51/1.89  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.51/1.89  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.51/1.89  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.51/1.89  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.51/1.89  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.51/1.89  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.51/1.89  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.51/1.89  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.51/1.89  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.51/1.89  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_114, plain, (![B_288, A_289]: (l1_pre_topc(B_288) | ~m1_pre_topc(B_288, A_289) | ~l1_pre_topc(A_289))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.51/1.89  tff(c_123, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_114])).
% 4.51/1.89  tff(c_130, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_123])).
% 4.51/1.89  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.51/1.89  tff(c_91, plain, (![A_286]: (u1_struct_0(A_286)=k2_struct_0(A_286) | ~l1_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.51/1.89  tff(c_95, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_12, c_91])).
% 4.51/1.89  tff(c_138, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_95])).
% 4.51/1.89  tff(c_96, plain, (![A_287]: (u1_struct_0(A_287)=k2_struct_0(A_287) | ~l1_pre_topc(A_287))), inference(resolution, [status(thm)], [c_12, c_91])).
% 4.51/1.89  tff(c_104, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_96])).
% 4.51/1.89  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_109, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_54])).
% 4.51/1.89  tff(c_147, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_109])).
% 4.51/1.89  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_145, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_52])).
% 4.51/1.89  tff(c_146, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_145])).
% 4.51/1.89  tff(c_120, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_114])).
% 4.51/1.89  tff(c_127, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_120])).
% 4.51/1.89  tff(c_134, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_127, c_95])).
% 4.51/1.89  tff(c_182, plain, (![B_295, A_296]: (r1_tarski(u1_struct_0(B_295), u1_struct_0(A_296)) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.89  tff(c_190, plain, (![B_295]: (r1_tarski(u1_struct_0(B_295), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_295, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_182])).
% 4.51/1.89  tff(c_218, plain, (![B_297]: (r1_tarski(u1_struct_0(B_297), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_297, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_190])).
% 4.51/1.89  tff(c_226, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_134, c_218])).
% 4.51/1.89  tff(c_478, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_226])).
% 4.51/1.89  tff(c_30, plain, (![A_25]: (m1_pre_topc(A_25, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.51/1.89  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_139, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_50])).
% 4.51/1.89  tff(c_603, plain, (![A_321, B_322]: (m1_pre_topc(A_321, g1_pre_topc(u1_struct_0(B_322), u1_pre_topc(B_322))) | ~m1_pre_topc(A_321, B_322) | ~l1_pre_topc(B_322) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.51/1.89  tff(c_624, plain, (![A_321]: (m1_pre_topc(A_321, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_321, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_321))), inference(superposition, [status(thm), theory('equality')], [c_134, c_603])).
% 4.51/1.89  tff(c_646, plain, (![A_323]: (m1_pre_topc(A_323, '#skF_4') | ~m1_pre_topc(A_323, '#skF_3') | ~l1_pre_topc(A_323))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_139, c_624])).
% 4.51/1.89  tff(c_660, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_646])).
% 4.51/1.89  tff(c_671, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_660])).
% 4.51/1.89  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_478, c_671])).
% 4.51/1.89  tff(c_675, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_226])).
% 4.51/1.89  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_148, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_48])).
% 4.51/1.89  tff(c_354, plain, (![A_307, B_308]: (m1_pre_topc(A_307, B_308) | ~m1_pre_topc(A_307, g1_pre_topc(u1_struct_0(B_308), u1_pre_topc(B_308))) | ~l1_pre_topc(B_308) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.51/1.89  tff(c_360, plain, (![A_307]: (m1_pre_topc(A_307, '#skF_3') | ~m1_pre_topc(A_307, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_307))), inference(superposition, [status(thm), theory('equality')], [c_134, c_354])).
% 4.51/1.89  tff(c_380, plain, (![A_309]: (m1_pre_topc(A_309, '#skF_3') | ~m1_pre_topc(A_309, '#skF_4') | ~l1_pre_topc(A_309))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_139, c_360])).
% 4.51/1.89  tff(c_196, plain, (![B_295]: (r1_tarski(u1_struct_0(B_295), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_295, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_182])).
% 4.51/1.89  tff(c_295, plain, (![B_301]: (r1_tarski(u1_struct_0(B_301), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_301, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_196])).
% 4.51/1.89  tff(c_300, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_138, c_295])).
% 4.51/1.89  tff(c_330, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_300])).
% 4.51/1.89  tff(c_392, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_380, c_330])).
% 4.51/1.89  tff(c_409, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_392])).
% 4.51/1.89  tff(c_418, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_409])).
% 4.51/1.89  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_418])).
% 4.51/1.89  tff(c_423, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_300])).
% 4.51/1.89  tff(c_674, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_226])).
% 4.51/1.89  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.89  tff(c_692, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_674, c_2])).
% 4.51/1.89  tff(c_695, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_423, c_692])).
% 4.51/1.89  tff(c_710, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_134])).
% 4.51/1.89  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_217])).
% 4.51/1.89  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 4.51/1.89  tff(c_1533, plain, (![D_365, C_364, E_368, A_367, G_369, B_366]: (r1_tmap_1(D_365, B_366, E_368, G_369) | ~r1_tmap_1(C_364, B_366, k3_tmap_1(A_367, B_366, D_365, C_364, E_368), G_369) | ~m1_subset_1(G_369, u1_struct_0(C_364)) | ~m1_subset_1(G_369, u1_struct_0(D_365)) | ~m1_pre_topc(C_364, D_365) | ~v1_tsep_1(C_364, D_365) | ~m1_subset_1(E_368, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_365), u1_struct_0(B_366)))) | ~v1_funct_2(E_368, u1_struct_0(D_365), u1_struct_0(B_366)) | ~v1_funct_1(E_368) | ~m1_pre_topc(D_365, A_367) | v2_struct_0(D_365) | ~m1_pre_topc(C_364, A_367) | v2_struct_0(C_364) | ~l1_pre_topc(B_366) | ~v2_pre_topc(B_366) | v2_struct_0(B_366) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367) | v2_struct_0(A_367))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.51/1.89  tff(c_1535, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_1533])).
% 4.51/1.89  tff(c_1538, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_147, c_104, c_138, c_146, c_104, c_138, c_675, c_148, c_138, c_148, c_710, c_1535])).
% 4.51/1.89  tff(c_1539, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_40, c_1538])).
% 4.51/1.89  tff(c_165, plain, (![B_293, A_294]: (v2_pre_topc(B_293) | ~m1_pre_topc(B_293, A_294) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.51/1.89  tff(c_174, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_165])).
% 4.51/1.89  tff(c_181, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_174])).
% 4.51/1.89  tff(c_20, plain, (![A_14]: (v3_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.51/1.89  tff(c_28, plain, (![B_24, A_22]: (m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.51/1.89  tff(c_1072, plain, (![B_339, A_340]: (v1_tsep_1(B_339, A_340) | ~v3_pre_topc(u1_struct_0(B_339), A_340) | ~m1_subset_1(u1_struct_0(B_339), k1_zfmisc_1(u1_struct_0(A_340))) | ~m1_pre_topc(B_339, A_340) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.51/1.89  tff(c_1985, plain, (![B_400, A_401]: (v1_tsep_1(B_400, A_401) | ~v3_pre_topc(u1_struct_0(B_400), A_401) | ~v2_pre_topc(A_401) | ~m1_pre_topc(B_400, A_401) | ~l1_pre_topc(A_401))), inference(resolution, [status(thm)], [c_28, c_1072])).
% 4.51/1.89  tff(c_2486, plain, (![A_436]: (v1_tsep_1('#skF_3', A_436) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_436) | ~v2_pre_topc(A_436) | ~m1_pre_topc('#skF_3', A_436) | ~l1_pre_topc(A_436))), inference(superposition, [status(thm), theory('equality')], [c_710, c_1985])).
% 4.51/1.89  tff(c_2499, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_2486])).
% 4.51/1.89  tff(c_2507, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_130, c_675, c_2499])).
% 4.51/1.89  tff(c_2509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1539, c_2507])).
% 4.51/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.89  
% 4.51/1.89  Inference rules
% 4.51/1.89  ----------------------
% 4.51/1.89  #Ref     : 0
% 4.51/1.89  #Sup     : 489
% 4.51/1.89  #Fact    : 0
% 4.51/1.89  #Define  : 0
% 4.51/1.89  #Split   : 22
% 4.51/1.89  #Chain   : 0
% 4.51/1.89  #Close   : 0
% 4.51/1.89  
% 4.51/1.89  Ordering : KBO
% 4.51/1.89  
% 4.51/1.89  Simplification rules
% 4.51/1.89  ----------------------
% 4.51/1.89  #Subsume      : 140
% 4.51/1.89  #Demod        : 746
% 4.51/1.89  #Tautology    : 162
% 4.51/1.89  #SimpNegUnit  : 23
% 4.51/1.89  #BackRed      : 13
% 4.51/1.89  
% 4.51/1.89  #Partial instantiations: 0
% 4.51/1.89  #Strategies tried      : 1
% 4.51/1.89  
% 4.51/1.89  Timing (in seconds)
% 4.51/1.89  ----------------------
% 4.51/1.89  Preprocessing        : 0.38
% 4.51/1.89  Parsing              : 0.20
% 4.51/1.89  CNF conversion       : 0.05
% 4.51/1.89  Main loop            : 0.68
% 4.51/1.89  Inferencing          : 0.22
% 4.51/1.89  Reduction            : 0.25
% 4.51/1.89  Demodulation         : 0.18
% 4.51/1.89  BG Simplification    : 0.03
% 4.51/1.89  Subsumption          : 0.14
% 4.51/1.89  Abstraction          : 0.03
% 4.51/1.89  MUC search           : 0.00
% 4.51/1.89  Cooper               : 0.00
% 4.51/1.89  Total                : 1.11
% 4.51/1.89  Index Insertion      : 0.00
% 4.51/1.89  Index Deletion       : 0.00
% 4.51/1.89  Index Matching       : 0.00
% 4.51/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
