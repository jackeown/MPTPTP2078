%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:43 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.45s
% Verified   : 
% Statistics : Number of formulae       :  143 (1021 expanded)
%              Number of leaves         :   43 ( 368 expanded)
%              Depth                    :   14
%              Number of atoms          :  323 (4700 expanded)
%              Number of equality atoms :   14 ( 510 expanded)
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

tff(f_242,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_193,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_89,axiom,(
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

tff(f_113,axiom,(
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

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_112,plain,(
    ! [B_295,A_296] :
      ( l1_pre_topc(B_295)
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_112])).

tff(c_128,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_121])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,(
    ! [A_293] :
      ( u1_struct_0(A_293) = k2_struct_0(A_293)
      | ~ l1_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_93])).

tff(c_94,plain,(
    ! [A_294] :
      ( u1_struct_0(A_294) = k2_struct_0(A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_102,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_94])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_107,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_54])).

tff(c_146,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_107])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_144,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_52])).

tff(c_145,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_144])).

tff(c_118,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_112])).

tff(c_125,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_118])).

tff(c_133,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_93])).

tff(c_173,plain,(
    ! [B_300,A_301] :
      ( r1_tarski(u1_struct_0(B_300),u1_struct_0(A_301))
      | ~ m1_pre_topc(B_300,A_301)
      | ~ l1_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_179,plain,(
    ! [B_300] :
      ( r1_tarski(u1_struct_0(B_300),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_300,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_173])).

tff(c_206,plain,(
    ! [B_302] :
      ( r1_tarski(u1_struct_0(B_302),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_302,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_179])).

tff(c_212,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_206])).

tff(c_348,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_30,plain,(
    ! [A_33] :
      ( m1_pre_topc(A_33,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_185,plain,(
    ! [B_300] :
      ( r1_tarski(u1_struct_0(B_300),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_300,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_173])).

tff(c_282,plain,(
    ! [B_307] :
      ( r1_tarski(u1_struct_0(B_307),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_307,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_185])).

tff(c_288,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_282])).

tff(c_510,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_516,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_510])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_516])).

tff(c_523,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_138,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_50])).

tff(c_524,plain,(
    ! [A_319,B_320] :
      ( m1_pre_topc(A_319,g1_pre_topc(u1_struct_0(B_320),u1_pre_topc(B_320)))
      | ~ m1_pre_topc(A_319,B_320)
      | ~ l1_pre_topc(B_320)
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_541,plain,(
    ! [A_319] :
      ( m1_pre_topc(A_319,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_319,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_524])).

tff(c_575,plain,(
    ! [A_321] :
      ( m1_pre_topc(A_321,'#skF_4')
      | ~ m1_pre_topc(A_321,'#skF_3')
      | ~ l1_pre_topc(A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_138,c_541])).

tff(c_578,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_523,c_575])).

tff(c_588,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_578])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_348,c_588])).

tff(c_592,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_147,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_48])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_139,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_77])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_1860,plain,(
    ! [G_392,A_391,E_390,B_389,C_393,D_394] :
      ( r1_tmap_1(D_394,B_389,E_390,G_392)
      | ~ r1_tmap_1(C_393,B_389,k3_tmap_1(A_391,B_389,D_394,C_393,E_390),G_392)
      | ~ m1_subset_1(G_392,u1_struct_0(C_393))
      | ~ m1_subset_1(G_392,u1_struct_0(D_394))
      | ~ m1_pre_topc(C_393,D_394)
      | ~ v1_tsep_1(C_393,D_394)
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_394),u1_struct_0(B_389))))
      | ~ v1_funct_2(E_390,u1_struct_0(D_394),u1_struct_0(B_389))
      | ~ v1_funct_1(E_390)
      | ~ m1_pre_topc(D_394,A_391)
      | v2_struct_0(D_394)
      | ~ m1_pre_topc(C_393,A_391)
      | v2_struct_0(C_393)
      | ~ l1_pre_topc(B_389)
      | ~ v2_pre_topc(B_389)
      | v2_struct_0(B_389)
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1862,plain,
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
    inference(resolution,[status(thm)],[c_78,c_1860])).

tff(c_1865,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_146,c_102,c_137,c_145,c_102,c_137,c_592,c_147,c_137,c_139,c_133,c_1862])).

tff(c_1866,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_40,c_1865])).

tff(c_639,plain,(
    ! [B_322,A_323] :
      ( m1_pre_topc(B_322,A_323)
      | ~ m1_pre_topc(B_322,g1_pre_topc(u1_struct_0(A_323),u1_pre_topc(A_323)))
      | ~ l1_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_645,plain,(
    ! [B_322] :
      ( m1_pre_topc(B_322,'#skF_3')
      | ~ m1_pre_topc(B_322,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_639])).

tff(c_659,plain,(
    ! [B_322] :
      ( m1_pre_topc(B_322,'#skF_3')
      | ~ m1_pre_topc(B_322,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_138,c_645])).

tff(c_833,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_836,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_659,c_833])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_836])).

tff(c_845,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_156,plain,(
    ! [B_298,A_299] :
      ( v2_pre_topc(B_298)
      | ~ m1_pre_topc(B_298,A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_162,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_169,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_162])).

tff(c_16,plain,(
    ! [A_15] :
      ( v3_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(u1_struct_0(B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_985,plain,(
    ! [B_336,A_337] :
      ( v1_tsep_1(B_336,A_337)
      | ~ v3_pre_topc(u1_struct_0(B_336),A_337)
      | ~ m1_subset_1(u1_struct_0(B_336),k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ m1_pre_topc(B_336,A_337)
      | ~ l1_pre_topc(A_337)
      | ~ v2_pre_topc(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1814,plain,(
    ! [B_383,A_384] :
      ( v1_tsep_1(B_383,A_384)
      | ~ v3_pre_topc(u1_struct_0(B_383),A_384)
      | ~ v2_pre_topc(A_384)
      | ~ m1_pre_topc(B_383,A_384)
      | ~ l1_pre_topc(A_384) ) ),
    inference(resolution,[status(thm)],[c_28,c_985])).

tff(c_1852,plain,(
    ! [A_388] :
      ( v1_tsep_1('#skF_3',A_388)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_388)
      | ~ v2_pre_topc(A_388)
      | ~ m1_pre_topc('#skF_3',A_388)
      | ~ l1_pre_topc(A_388) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1814])).

tff(c_1856,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1852])).

tff(c_1859,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_125,c_845,c_1856])).

tff(c_209,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_206])).

tff(c_298,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_327,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_298])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_327])).

tff(c_333,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_285,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_282])).

tff(c_722,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_725,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_659,c_722])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_725])).

tff(c_731,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_32,plain,(
    ! [B_36,A_34] :
      ( r1_tarski(u1_struct_0(B_36),u1_struct_0(A_34))
      | ~ m1_pre_topc(B_36,A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1267,plain,(
    ! [B_351,C_352,A_353] :
      ( v1_tsep_1(B_351,C_352)
      | ~ r1_tarski(u1_struct_0(B_351),u1_struct_0(C_352))
      | ~ m1_pre_topc(C_352,A_353)
      | v2_struct_0(C_352)
      | ~ m1_pre_topc(B_351,A_353)
      | ~ v1_tsep_1(B_351,A_353)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2906,plain,(
    ! [B_446,A_447,A_448] :
      ( v1_tsep_1(B_446,A_447)
      | ~ m1_pre_topc(A_447,A_448)
      | v2_struct_0(A_447)
      | ~ m1_pre_topc(B_446,A_448)
      | ~ v1_tsep_1(B_446,A_448)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | v2_struct_0(A_448)
      | ~ m1_pre_topc(B_446,A_447)
      | ~ l1_pre_topc(A_447) ) ),
    inference(resolution,[status(thm)],[c_32,c_1267])).

tff(c_2928,plain,(
    ! [B_446] :
      ( v1_tsep_1(B_446,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_446,'#skF_3')
      | ~ v1_tsep_1(B_446,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_446,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_731,c_2906])).

tff(c_2970,plain,(
    ! [B_446] :
      ( v1_tsep_1(B_446,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_446,'#skF_3')
      | ~ v1_tsep_1(B_446,'#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_446,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_169,c_125,c_2928])).

tff(c_3039,plain,(
    ! [B_453] :
      ( v1_tsep_1(B_453,'#skF_4')
      | ~ m1_pre_topc(B_453,'#skF_3')
      | ~ v1_tsep_1(B_453,'#skF_3')
      | ~ m1_pre_topc(B_453,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_2970])).

tff(c_3051,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1859,c_3039])).

tff(c_3059,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_845,c_3051])).

tff(c_3061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1866,c_3059])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/1.96  
% 5.10/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.10/1.97  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.10/1.97  
% 5.10/1.97  %Foreground sorts:
% 5.10/1.97  
% 5.10/1.97  
% 5.10/1.97  %Background operators:
% 5.10/1.97  
% 5.10/1.97  
% 5.10/1.97  %Foreground operators:
% 5.10/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.10/1.97  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.10/1.97  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.10/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.10/1.97  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.10/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.97  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.10/1.97  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.10/1.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.10/1.97  tff('#skF_7', type, '#skF_7': $i).
% 5.10/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.10/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.10/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.10/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.10/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.10/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.10/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.10/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.10/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.10/1.97  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.10/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.10/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.10/1.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.10/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.10/1.97  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.10/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.97  
% 5.45/1.99  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.45/1.99  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.45/1.99  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.45/1.99  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.45/1.99  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 5.45/1.99  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.45/1.99  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.45/1.99  tff(f_193, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 5.45/1.99  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.45/1.99  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.45/1.99  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.45/1.99  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.45/1.99  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 5.45/1.99  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 5.45/1.99  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_112, plain, (![B_295, A_296]: (l1_pre_topc(B_295) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.45/1.99  tff(c_121, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_112])).
% 5.45/1.99  tff(c_128, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_121])).
% 5.45/1.99  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.45/1.99  tff(c_89, plain, (![A_293]: (u1_struct_0(A_293)=k2_struct_0(A_293) | ~l1_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.45/1.99  tff(c_93, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_89])).
% 5.45/1.99  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_128, c_93])).
% 5.45/1.99  tff(c_94, plain, (![A_294]: (u1_struct_0(A_294)=k2_struct_0(A_294) | ~l1_pre_topc(A_294))), inference(resolution, [status(thm)], [c_6, c_89])).
% 5.45/1.99  tff(c_102, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_94])).
% 5.45/1.99  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_107, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_54])).
% 5.45/1.99  tff(c_146, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 5.45/1.99  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_144, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_52])).
% 5.45/1.99  tff(c_145, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_144])).
% 5.45/1.99  tff(c_118, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_112])).
% 5.45/1.99  tff(c_125, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_118])).
% 5.45/1.99  tff(c_133, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_125, c_93])).
% 5.45/1.99  tff(c_173, plain, (![B_300, A_301]: (r1_tarski(u1_struct_0(B_300), u1_struct_0(A_301)) | ~m1_pre_topc(B_300, A_301) | ~l1_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.45/1.99  tff(c_179, plain, (![B_300]: (r1_tarski(u1_struct_0(B_300), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_300, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_173])).
% 5.45/1.99  tff(c_206, plain, (![B_302]: (r1_tarski(u1_struct_0(B_302), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_302, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_179])).
% 5.45/1.99  tff(c_212, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_206])).
% 5.45/1.99  tff(c_348, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_212])).
% 5.45/1.99  tff(c_30, plain, (![A_33]: (m1_pre_topc(A_33, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.45/1.99  tff(c_185, plain, (![B_300]: (r1_tarski(u1_struct_0(B_300), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_300, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_173])).
% 5.45/1.99  tff(c_282, plain, (![B_307]: (r1_tarski(u1_struct_0(B_307), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_307, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_185])).
% 5.45/1.99  tff(c_288, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_282])).
% 5.45/1.99  tff(c_510, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_288])).
% 5.45/1.99  tff(c_516, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_510])).
% 5.45/1.99  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_516])).
% 5.45/1.99  tff(c_523, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_288])).
% 5.45/1.99  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_138, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_50])).
% 5.45/1.99  tff(c_524, plain, (![A_319, B_320]: (m1_pre_topc(A_319, g1_pre_topc(u1_struct_0(B_320), u1_pre_topc(B_320))) | ~m1_pre_topc(A_319, B_320) | ~l1_pre_topc(B_320) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.45/1.99  tff(c_541, plain, (![A_319]: (m1_pre_topc(A_319, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_319, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_319))), inference(superposition, [status(thm), theory('equality')], [c_133, c_524])).
% 5.45/1.99  tff(c_575, plain, (![A_321]: (m1_pre_topc(A_321, '#skF_4') | ~m1_pre_topc(A_321, '#skF_3') | ~l1_pre_topc(A_321))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_138, c_541])).
% 5.45/1.99  tff(c_578, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_523, c_575])).
% 5.45/1.99  tff(c_588, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_578])).
% 5.45/1.99  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_348, c_588])).
% 5.45/1.99  tff(c_592, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_212])).
% 5.45/1.99  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_147, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_48])).
% 5.45/1.99  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 5.45/1.99  tff(c_139, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_77])).
% 5.45/1.99  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_242])).
% 5.45/1.99  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 5.45/1.99  tff(c_1860, plain, (![G_392, A_391, E_390, B_389, C_393, D_394]: (r1_tmap_1(D_394, B_389, E_390, G_392) | ~r1_tmap_1(C_393, B_389, k3_tmap_1(A_391, B_389, D_394, C_393, E_390), G_392) | ~m1_subset_1(G_392, u1_struct_0(C_393)) | ~m1_subset_1(G_392, u1_struct_0(D_394)) | ~m1_pre_topc(C_393, D_394) | ~v1_tsep_1(C_393, D_394) | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_394), u1_struct_0(B_389)))) | ~v1_funct_2(E_390, u1_struct_0(D_394), u1_struct_0(B_389)) | ~v1_funct_1(E_390) | ~m1_pre_topc(D_394, A_391) | v2_struct_0(D_394) | ~m1_pre_topc(C_393, A_391) | v2_struct_0(C_393) | ~l1_pre_topc(B_389) | ~v2_pre_topc(B_389) | v2_struct_0(B_389) | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_193])).
% 5.45/1.99  tff(c_1862, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_78, c_1860])).
% 5.45/1.99  tff(c_1865, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_146, c_102, c_137, c_145, c_102, c_137, c_592, c_147, c_137, c_139, c_133, c_1862])).
% 5.45/1.99  tff(c_1866, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_40, c_1865])).
% 5.45/1.99  tff(c_639, plain, (![B_322, A_323]: (m1_pre_topc(B_322, A_323) | ~m1_pre_topc(B_322, g1_pre_topc(u1_struct_0(A_323), u1_pre_topc(A_323))) | ~l1_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.45/1.99  tff(c_645, plain, (![B_322]: (m1_pre_topc(B_322, '#skF_3') | ~m1_pre_topc(B_322, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_639])).
% 5.45/1.99  tff(c_659, plain, (![B_322]: (m1_pre_topc(B_322, '#skF_3') | ~m1_pre_topc(B_322, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_138, c_645])).
% 5.45/1.99  tff(c_833, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_288])).
% 5.45/1.99  tff(c_836, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_659, c_833])).
% 5.45/1.99  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_592, c_836])).
% 5.45/1.99  tff(c_845, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_288])).
% 5.45/1.99  tff(c_156, plain, (![B_298, A_299]: (v2_pre_topc(B_298) | ~m1_pre_topc(B_298, A_299) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.45/1.99  tff(c_162, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_156])).
% 5.45/1.99  tff(c_169, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_162])).
% 5.45/1.99  tff(c_16, plain, (![A_15]: (v3_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.45/1.99  tff(c_28, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.45/1.99  tff(c_985, plain, (![B_336, A_337]: (v1_tsep_1(B_336, A_337) | ~v3_pre_topc(u1_struct_0(B_336), A_337) | ~m1_subset_1(u1_struct_0(B_336), k1_zfmisc_1(u1_struct_0(A_337))) | ~m1_pre_topc(B_336, A_337) | ~l1_pre_topc(A_337) | ~v2_pre_topc(A_337))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.45/1.99  tff(c_1814, plain, (![B_383, A_384]: (v1_tsep_1(B_383, A_384) | ~v3_pre_topc(u1_struct_0(B_383), A_384) | ~v2_pre_topc(A_384) | ~m1_pre_topc(B_383, A_384) | ~l1_pre_topc(A_384))), inference(resolution, [status(thm)], [c_28, c_985])).
% 5.45/1.99  tff(c_1852, plain, (![A_388]: (v1_tsep_1('#skF_3', A_388) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_388) | ~v2_pre_topc(A_388) | ~m1_pre_topc('#skF_3', A_388) | ~l1_pre_topc(A_388))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1814])).
% 5.45/1.99  tff(c_1856, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1852])).
% 5.45/1.99  tff(c_1859, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_125, c_845, c_1856])).
% 5.45/1.99  tff(c_209, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_206])).
% 5.45/1.99  tff(c_298, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_209])).
% 5.45/1.99  tff(c_327, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_298])).
% 5.45/1.99  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_327])).
% 5.45/1.99  tff(c_333, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_209])).
% 5.45/1.99  tff(c_285, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_137, c_282])).
% 5.45/1.99  tff(c_722, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_285])).
% 5.45/1.99  tff(c_725, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_659, c_722])).
% 5.45/1.99  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_333, c_725])).
% 5.45/1.99  tff(c_731, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_285])).
% 5.45/1.99  tff(c_32, plain, (![B_36, A_34]: (r1_tarski(u1_struct_0(B_36), u1_struct_0(A_34)) | ~m1_pre_topc(B_36, A_34) | ~l1_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.45/1.99  tff(c_1267, plain, (![B_351, C_352, A_353]: (v1_tsep_1(B_351, C_352) | ~r1_tarski(u1_struct_0(B_351), u1_struct_0(C_352)) | ~m1_pre_topc(C_352, A_353) | v2_struct_0(C_352) | ~m1_pre_topc(B_351, A_353) | ~v1_tsep_1(B_351, A_353) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.45/1.99  tff(c_2906, plain, (![B_446, A_447, A_448]: (v1_tsep_1(B_446, A_447) | ~m1_pre_topc(A_447, A_448) | v2_struct_0(A_447) | ~m1_pre_topc(B_446, A_448) | ~v1_tsep_1(B_446, A_448) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | v2_struct_0(A_448) | ~m1_pre_topc(B_446, A_447) | ~l1_pre_topc(A_447))), inference(resolution, [status(thm)], [c_32, c_1267])).
% 5.45/1.99  tff(c_2928, plain, (![B_446]: (v1_tsep_1(B_446, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_446, '#skF_3') | ~v1_tsep_1(B_446, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_446, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_731, c_2906])).
% 5.45/1.99  tff(c_2970, plain, (![B_446]: (v1_tsep_1(B_446, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_446, '#skF_3') | ~v1_tsep_1(B_446, '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_446, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_169, c_125, c_2928])).
% 5.45/1.99  tff(c_3039, plain, (![B_453]: (v1_tsep_1(B_453, '#skF_4') | ~m1_pre_topc(B_453, '#skF_3') | ~v1_tsep_1(B_453, '#skF_3') | ~m1_pre_topc(B_453, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_2970])).
% 5.45/1.99  tff(c_3051, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1859, c_3039])).
% 5.45/1.99  tff(c_3059, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_592, c_845, c_3051])).
% 5.45/1.99  tff(c_3061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1866, c_3059])).
% 5.45/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.45/1.99  
% 5.45/1.99  Inference rules
% 5.45/1.99  ----------------------
% 5.45/1.99  #Ref     : 0
% 5.45/1.99  #Sup     : 606
% 5.45/1.99  #Fact    : 0
% 5.45/1.99  #Define  : 0
% 5.45/1.99  #Split   : 22
% 5.45/1.99  #Chain   : 0
% 5.45/1.99  #Close   : 0
% 5.45/1.99  
% 5.45/1.99  Ordering : KBO
% 5.45/1.99  
% 5.45/1.99  Simplification rules
% 5.45/1.99  ----------------------
% 5.45/1.99  #Subsume      : 158
% 5.45/1.99  #Demod        : 793
% 5.45/1.99  #Tautology    : 192
% 5.45/1.99  #SimpNegUnit  : 58
% 5.45/1.99  #BackRed      : 6
% 5.45/1.99  
% 5.45/1.99  #Partial instantiations: 0
% 5.45/1.99  #Strategies tried      : 1
% 5.45/1.99  
% 5.45/1.99  Timing (in seconds)
% 5.45/1.99  ----------------------
% 5.45/1.99  Preprocessing        : 0.39
% 5.45/1.99  Parsing              : 0.20
% 5.45/1.99  CNF conversion       : 0.05
% 5.45/1.99  Main loop            : 0.80
% 5.45/1.99  Inferencing          : 0.25
% 5.45/1.99  Reduction            : 0.29
% 5.45/1.99  Demodulation         : 0.21
% 5.45/1.99  BG Simplification    : 0.03
% 5.45/2.00  Subsumption          : 0.16
% 5.45/2.00  Abstraction          : 0.03
% 5.45/2.00  MUC search           : 0.00
% 5.45/2.00  Cooper               : 0.00
% 5.45/2.00  Total                : 1.24
% 5.45/2.00  Index Insertion      : 0.00
% 5.45/2.00  Index Deletion       : 0.00
% 5.45/2.00  Index Matching       : 0.00
% 5.45/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
