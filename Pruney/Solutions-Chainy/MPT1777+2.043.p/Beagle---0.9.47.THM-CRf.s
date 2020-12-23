%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:38 EST 2020

% Result     : Theorem 5.68s
% Output     : CNFRefutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 730 expanded)
%              Number of leaves         :   45 ( 273 expanded)
%              Depth                    :   15
%              Number of atoms          :  291 (3409 expanded)
%              Number of equality atoms :   24 ( 390 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(f_140,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_86,axiom,(
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

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_116,plain,(
    ! [B_298,A_299] :
      ( l1_pre_topc(B_298)
      | ~ m1_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_132,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_125])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    ! [A_296] :
      ( u1_struct_0(A_296) = k2_struct_0(A_296)
      | ~ l1_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_140,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_93])).

tff(c_98,plain,(
    ! [A_297] :
      ( u1_struct_0(A_297) = k2_struct_0(A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_106,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_98])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_111,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_56])).

tff(c_149,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_111])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_147,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_54])).

tff(c_148,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_147])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_129,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_122])).

tff(c_136,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_93])).

tff(c_184,plain,(
    ! [B_305,A_306] :
      ( r1_tarski(u1_struct_0(B_305),u1_struct_0(A_306))
      | ~ m1_pre_topc(B_305,A_306)
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_192,plain,(
    ! [B_305] :
      ( r1_tarski(u1_struct_0(B_305),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_305,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_184])).

tff(c_220,plain,(
    ! [B_307] :
      ( r1_tarski(u1_struct_0(B_307),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_307,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_192])).

tff(c_228,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_220])).

tff(c_480,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_141,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_52])).

tff(c_481,plain,(
    ! [A_322,B_323] :
      ( k1_tsep_1(A_322,B_323,B_323) = g1_pre_topc(u1_struct_0(B_323),u1_pre_topc(B_323))
      | ~ m1_pre_topc(B_323,A_322)
      | v2_struct_0(B_323)
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322)
      | v2_struct_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_489,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_481])).

tff(c_503,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_141,c_136,c_489])).

tff(c_504,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_503])).

tff(c_785,plain,(
    ! [B_332,A_333,C_334] :
      ( m1_pre_topc(B_332,k1_tsep_1(A_333,B_332,C_334))
      | ~ m1_pre_topc(C_334,A_333)
      | v2_struct_0(C_334)
      | ~ m1_pre_topc(B_332,A_333)
      | v2_struct_0(B_332)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333)
      | v2_struct_0(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_804,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_785])).

tff(c_816,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_64,c_804])).

tff(c_818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_480,c_816])).

tff(c_820,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_150,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_50])).

tff(c_32,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_334,plain,(
    ! [B_313,A_314] :
      ( m1_pre_topc(B_313,A_314)
      | ~ m1_pre_topc(B_313,g1_pre_topc(u1_struct_0(A_314),u1_pre_topc(A_314)))
      | ~ l1_pre_topc(A_314) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_340,plain,(
    ! [B_313] :
      ( m1_pre_topc(B_313,'#skF_3')
      | ~ m1_pre_topc(B_313,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_334])).

tff(c_354,plain,(
    ! [B_313] :
      ( m1_pre_topc(B_313,'#skF_3')
      | ~ m1_pre_topc(B_313,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_141,c_340])).

tff(c_198,plain,(
    ! [B_305] :
      ( r1_tarski(u1_struct_0(B_305),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_305,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_184])).

tff(c_315,plain,(
    ! [B_312] :
      ( r1_tarski(u1_struct_0(B_312),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_312,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_198])).

tff(c_320,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_315])).

tff(c_409,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_413,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_354,c_409])).

tff(c_455,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_413])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_455])).

tff(c_460,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_819,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_847,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_819,c_2])).

tff(c_850,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_847])).

tff(c_857,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_136])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_1574,plain,(
    ! [B_363,C_365,A_366,D_364,G_367,E_362] :
      ( r1_tmap_1(D_364,B_363,E_362,G_367)
      | ~ r1_tmap_1(C_365,B_363,k3_tmap_1(A_366,B_363,D_364,C_365,E_362),G_367)
      | ~ m1_subset_1(G_367,u1_struct_0(C_365))
      | ~ m1_subset_1(G_367,u1_struct_0(D_364))
      | ~ m1_pre_topc(C_365,D_364)
      | ~ v1_tsep_1(C_365,D_364)
      | ~ m1_subset_1(E_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_364),u1_struct_0(B_363))))
      | ~ v1_funct_2(E_362,u1_struct_0(D_364),u1_struct_0(B_363))
      | ~ v1_funct_1(E_362)
      | ~ m1_pre_topc(D_364,A_366)
      | v2_struct_0(D_364)
      | ~ m1_pre_topc(C_365,A_366)
      | v2_struct_0(C_365)
      | ~ l1_pre_topc(B_363)
      | ~ v2_pre_topc(B_363)
      | v2_struct_0(B_363)
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366)
      | v2_struct_0(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_1576,plain,
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
    inference(resolution,[status(thm)],[c_80,c_1574])).

tff(c_1579,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_149,c_106,c_140,c_148,c_106,c_140,c_820,c_150,c_140,c_150,c_857,c_1576])).

tff(c_1580,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_42,c_1579])).

tff(c_167,plain,(
    ! [B_303,A_304] :
      ( v2_pre_topc(B_303)
      | ~ m1_pre_topc(B_303,A_304)
      | ~ l1_pre_topc(A_304)
      | ~ v2_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_176,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_167])).

tff(c_183,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_176])).

tff(c_18,plain,(
    ! [A_14] :
      ( v3_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [B_24,A_22] :
      ( m1_subset_1(u1_struct_0(B_24),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_929,plain,(
    ! [B_336,A_337] :
      ( v1_tsep_1(B_336,A_337)
      | ~ v3_pre_topc(u1_struct_0(B_336),A_337)
      | ~ m1_subset_1(u1_struct_0(B_336),k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ m1_pre_topc(B_336,A_337)
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1930,plain,(
    ! [B_381,A_382] :
      ( v1_tsep_1(B_381,A_382)
      | ~ v3_pre_topc(u1_struct_0(B_381),A_382)
      | ~ v2_pre_topc(A_382)
      | ~ m1_pre_topc(B_381,A_382)
      | ~ l1_pre_topc(A_382) ) ),
    inference(resolution,[status(thm)],[c_26,c_929])).

tff(c_3254,plain,(
    ! [A_432] :
      ( v1_tsep_1('#skF_3',A_432)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_432)
      | ~ v2_pre_topc(A_432)
      | ~ m1_pre_topc('#skF_3',A_432)
      | ~ l1_pre_topc(A_432) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_1930])).

tff(c_3267,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_3254])).

tff(c_3275,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_132,c_820,c_3267])).

tff(c_3277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1580,c_3275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:18:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.68/2.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.01  
% 5.68/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.01  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.68/2.01  
% 5.68/2.01  %Foreground sorts:
% 5.68/2.01  
% 5.68/2.01  
% 5.68/2.01  %Background operators:
% 5.68/2.01  
% 5.68/2.01  
% 5.68/2.01  %Foreground operators:
% 5.68/2.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.68/2.01  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 5.68/2.01  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.68/2.01  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.68/2.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.68/2.01  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.68/2.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.68/2.01  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.68/2.01  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.68/2.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.68/2.01  tff('#skF_7', type, '#skF_7': $i).
% 5.68/2.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.68/2.01  tff('#skF_5', type, '#skF_5': $i).
% 5.68/2.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.68/2.01  tff('#skF_6', type, '#skF_6': $i).
% 5.68/2.01  tff('#skF_2', type, '#skF_2': $i).
% 5.68/2.01  tff('#skF_3', type, '#skF_3': $i).
% 5.68/2.01  tff('#skF_1', type, '#skF_1': $i).
% 5.68/2.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.68/2.01  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.68/2.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.68/2.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.68/2.01  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.68/2.01  tff('#skF_4', type, '#skF_4': $i).
% 5.68/2.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.68/2.01  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.68/2.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.68/2.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.68/2.01  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.68/2.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.68/2.01  
% 5.68/2.03  tff(f_251, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.68/2.03  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.68/2.03  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.68/2.03  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.68/2.03  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 5.68/2.03  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 5.68/2.03  tff(f_114, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 5.68/2.03  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.68/2.03  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.68/2.03  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.68/2.03  tff(f_202, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 5.68/2.03  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.68/2.03  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.68/2.03  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.68/2.03  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.68/2.03  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_116, plain, (![B_298, A_299]: (l1_pre_topc(B_298) | ~m1_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.68/2.03  tff(c_125, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_116])).
% 5.68/2.03  tff(c_132, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_125])).
% 5.68/2.03  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.68/2.03  tff(c_89, plain, (![A_296]: (u1_struct_0(A_296)=k2_struct_0(A_296) | ~l1_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.68/2.03  tff(c_93, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_12, c_89])).
% 5.68/2.03  tff(c_140, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_132, c_93])).
% 5.68/2.03  tff(c_98, plain, (![A_297]: (u1_struct_0(A_297)=k2_struct_0(A_297) | ~l1_pre_topc(A_297))), inference(resolution, [status(thm)], [c_12, c_89])).
% 5.68/2.03  tff(c_106, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_98])).
% 5.68/2.03  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_111, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_56])).
% 5.68/2.03  tff(c_149, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_111])).
% 5.68/2.03  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_147, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_54])).
% 5.68/2.03  tff(c_148, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_147])).
% 5.68/2.03  tff(c_122, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_116])).
% 5.68/2.03  tff(c_129, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_122])).
% 5.68/2.03  tff(c_136, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_129, c_93])).
% 5.68/2.03  tff(c_184, plain, (![B_305, A_306]: (r1_tarski(u1_struct_0(B_305), u1_struct_0(A_306)) | ~m1_pre_topc(B_305, A_306) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_140])).
% 5.68/2.03  tff(c_192, plain, (![B_305]: (r1_tarski(u1_struct_0(B_305), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_305, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_184])).
% 5.68/2.03  tff(c_220, plain, (![B_307]: (r1_tarski(u1_struct_0(B_307), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_307, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_192])).
% 5.68/2.03  tff(c_228, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_136, c_220])).
% 5.68/2.03  tff(c_480, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_228])).
% 5.68/2.03  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_141, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_52])).
% 5.68/2.03  tff(c_481, plain, (![A_322, B_323]: (k1_tsep_1(A_322, B_323, B_323)=g1_pre_topc(u1_struct_0(B_323), u1_pre_topc(B_323)) | ~m1_pre_topc(B_323, A_322) | v2_struct_0(B_323) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322) | v2_struct_0(A_322))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.68/2.03  tff(c_489, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_481])).
% 5.68/2.03  tff(c_503, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4' | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_141, c_136, c_489])).
% 5.68/2.03  tff(c_504, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_503])).
% 5.68/2.03  tff(c_785, plain, (![B_332, A_333, C_334]: (m1_pre_topc(B_332, k1_tsep_1(A_333, B_332, C_334)) | ~m1_pre_topc(C_334, A_333) | v2_struct_0(C_334) | ~m1_pre_topc(B_332, A_333) | v2_struct_0(B_332) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333) | v2_struct_0(A_333))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.68/2.03  tff(c_804, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_504, c_785])).
% 5.68/2.03  tff(c_816, plain, (m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_64, c_804])).
% 5.68/2.03  tff(c_818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_480, c_816])).
% 5.68/2.03  tff(c_820, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_228])).
% 5.68/2.03  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_150, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_50])).
% 5.68/2.03  tff(c_32, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.68/2.03  tff(c_334, plain, (![B_313, A_314]: (m1_pre_topc(B_313, A_314) | ~m1_pre_topc(B_313, g1_pre_topc(u1_struct_0(A_314), u1_pre_topc(A_314))) | ~l1_pre_topc(A_314))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.68/2.03  tff(c_340, plain, (![B_313]: (m1_pre_topc(B_313, '#skF_3') | ~m1_pre_topc(B_313, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_334])).
% 5.68/2.03  tff(c_354, plain, (![B_313]: (m1_pre_topc(B_313, '#skF_3') | ~m1_pre_topc(B_313, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_141, c_340])).
% 5.68/2.03  tff(c_198, plain, (![B_305]: (r1_tarski(u1_struct_0(B_305), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_305, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_184])).
% 5.68/2.03  tff(c_315, plain, (![B_312]: (r1_tarski(u1_struct_0(B_312), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_312, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_198])).
% 5.68/2.03  tff(c_320, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_315])).
% 5.68/2.03  tff(c_409, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_320])).
% 5.68/2.03  tff(c_413, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_354, c_409])).
% 5.68/2.03  tff(c_455, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_413])).
% 5.68/2.03  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_455])).
% 5.68/2.03  tff(c_460, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_320])).
% 5.68/2.03  tff(c_819, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_228])).
% 5.68/2.03  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.68/2.03  tff(c_847, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_819, c_2])).
% 5.68/2.03  tff(c_850, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_847])).
% 5.68/2.03  tff(c_857, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_850, c_136])).
% 5.68/2.03  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_251])).
% 5.68/2.03  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 5.68/2.03  tff(c_1574, plain, (![B_363, C_365, A_366, D_364, G_367, E_362]: (r1_tmap_1(D_364, B_363, E_362, G_367) | ~r1_tmap_1(C_365, B_363, k3_tmap_1(A_366, B_363, D_364, C_365, E_362), G_367) | ~m1_subset_1(G_367, u1_struct_0(C_365)) | ~m1_subset_1(G_367, u1_struct_0(D_364)) | ~m1_pre_topc(C_365, D_364) | ~v1_tsep_1(C_365, D_364) | ~m1_subset_1(E_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_364), u1_struct_0(B_363)))) | ~v1_funct_2(E_362, u1_struct_0(D_364), u1_struct_0(B_363)) | ~v1_funct_1(E_362) | ~m1_pre_topc(D_364, A_366) | v2_struct_0(D_364) | ~m1_pre_topc(C_365, A_366) | v2_struct_0(C_365) | ~l1_pre_topc(B_363) | ~v2_pre_topc(B_363) | v2_struct_0(B_363) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366) | v2_struct_0(A_366))), inference(cnfTransformation, [status(thm)], [f_202])).
% 5.68/2.03  tff(c_1576, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_1574])).
% 5.68/2.03  tff(c_1579, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_149, c_106, c_140, c_148, c_106, c_140, c_820, c_150, c_140, c_150, c_857, c_1576])).
% 5.68/2.03  tff(c_1580, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_42, c_1579])).
% 5.68/2.03  tff(c_167, plain, (![B_303, A_304]: (v2_pre_topc(B_303) | ~m1_pre_topc(B_303, A_304) | ~l1_pre_topc(A_304) | ~v2_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.68/2.03  tff(c_176, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_167])).
% 5.68/2.03  tff(c_183, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_176])).
% 5.68/2.03  tff(c_18, plain, (![A_14]: (v3_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.68/2.03  tff(c_26, plain, (![B_24, A_22]: (m1_subset_1(u1_struct_0(B_24), k1_zfmisc_1(u1_struct_0(A_22))) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.68/2.03  tff(c_929, plain, (![B_336, A_337]: (v1_tsep_1(B_336, A_337) | ~v3_pre_topc(u1_struct_0(B_336), A_337) | ~m1_subset_1(u1_struct_0(B_336), k1_zfmisc_1(u1_struct_0(A_337))) | ~m1_pre_topc(B_336, A_337) | ~l1_pre_topc(A_337) | ~v2_pre_topc(A_337))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.68/2.03  tff(c_1930, plain, (![B_381, A_382]: (v1_tsep_1(B_381, A_382) | ~v3_pre_topc(u1_struct_0(B_381), A_382) | ~v2_pre_topc(A_382) | ~m1_pre_topc(B_381, A_382) | ~l1_pre_topc(A_382))), inference(resolution, [status(thm)], [c_26, c_929])).
% 5.68/2.03  tff(c_3254, plain, (![A_432]: (v1_tsep_1('#skF_3', A_432) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_432) | ~v2_pre_topc(A_432) | ~m1_pre_topc('#skF_3', A_432) | ~l1_pre_topc(A_432))), inference(superposition, [status(thm), theory('equality')], [c_857, c_1930])).
% 5.68/2.03  tff(c_3267, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_18, c_3254])).
% 5.68/2.03  tff(c_3275, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_132, c_820, c_3267])).
% 5.68/2.03  tff(c_3277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1580, c_3275])).
% 5.68/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.68/2.03  
% 5.68/2.03  Inference rules
% 5.68/2.03  ----------------------
% 5.68/2.03  #Ref     : 0
% 5.68/2.03  #Sup     : 657
% 5.68/2.03  #Fact    : 0
% 5.68/2.03  #Define  : 0
% 5.68/2.03  #Split   : 21
% 5.68/2.03  #Chain   : 0
% 5.68/2.03  #Close   : 0
% 5.68/2.03  
% 5.68/2.03  Ordering : KBO
% 5.68/2.03  
% 5.68/2.03  Simplification rules
% 5.68/2.03  ----------------------
% 5.68/2.03  #Subsume      : 171
% 5.68/2.03  #Demod        : 1028
% 5.68/2.03  #Tautology    : 236
% 5.68/2.03  #SimpNegUnit  : 94
% 5.68/2.03  #BackRed      : 19
% 5.68/2.03  
% 5.68/2.03  #Partial instantiations: 0
% 5.68/2.03  #Strategies tried      : 1
% 5.68/2.03  
% 5.68/2.03  Timing (in seconds)
% 5.68/2.03  ----------------------
% 5.68/2.04  Preprocessing        : 0.39
% 5.68/2.04  Parsing              : 0.20
% 5.68/2.04  CNF conversion       : 0.05
% 5.68/2.04  Main loop            : 0.87
% 5.68/2.04  Inferencing          : 0.28
% 5.68/2.04  Reduction            : 0.31
% 5.68/2.04  Demodulation         : 0.23
% 5.68/2.04  BG Simplification    : 0.03
% 5.68/2.04  Subsumption          : 0.18
% 5.68/2.04  Abstraction          : 0.03
% 5.68/2.04  MUC search           : 0.00
% 5.68/2.04  Cooper               : 0.00
% 5.68/2.04  Total                : 1.31
% 5.68/2.04  Index Insertion      : 0.00
% 5.68/2.04  Index Deletion       : 0.00
% 5.68/2.04  Index Matching       : 0.00
% 5.68/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
