%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:37 EST 2020

% Result     : Theorem 9.75s
% Output     : CNFRefutation 9.75s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 786 expanded)
%              Number of leaves         :   44 ( 292 expanded)
%              Depth                    :   16
%              Number of atoms          :  265 (3579 expanded)
%              Number of equality atoms :   19 ( 399 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_140,axiom,(
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

tff(f_121,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_114,axiom,(
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

tff(c_86,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_50,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_84,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_82,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_72,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_125,plain,(
    ! [B_295,A_296] :
      ( l1_pre_topc(B_295)
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_131,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_125])).

tff(c_138,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_131])).

tff(c_16,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_101,plain,(
    ! [A_291] :
      ( u1_struct_0(A_291) = k2_struct_0(A_291)
      | ~ l1_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_105,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_101])).

tff(c_145,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_105])).

tff(c_106,plain,(
    ! [A_292] :
      ( u1_struct_0(A_292) = k2_struct_0(A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(resolution,[status(thm)],[c_16,c_101])).

tff(c_114,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_106])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_119,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_64])).

tff(c_156,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_119])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_150,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_62])).

tff(c_155,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_150])).

tff(c_134,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_125])).

tff(c_141,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_134])).

tff(c_42,plain,(
    ! [A_33] :
      ( m1_pre_topc(A_33,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_149,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_105])).

tff(c_60,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_162,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_60])).

tff(c_771,plain,(
    ! [A_335,B_336] :
      ( m1_pre_topc(A_335,g1_pre_topc(u1_struct_0(B_336),u1_pre_topc(B_336)))
      | ~ m1_pre_topc(A_335,B_336)
      | ~ l1_pre_topc(B_336)
      | ~ l1_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_789,plain,(
    ! [A_335] :
      ( m1_pre_topc(A_335,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_335,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_335) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_771])).

tff(c_814,plain,(
    ! [A_337] :
      ( m1_pre_topc(A_337,'#skF_4')
      | ~ m1_pre_topc(A_337,'#skF_3')
      | ~ l1_pre_topc(A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_162,c_789])).

tff(c_828,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_814])).

tff(c_838,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_828])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_157,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_58])).

tff(c_485,plain,(
    ! [A_320,B_321] :
      ( m1_pre_topc(A_320,B_321)
      | ~ m1_pre_topc(A_320,g1_pre_topc(u1_struct_0(B_321),u1_pre_topc(B_321)))
      | ~ l1_pre_topc(B_321)
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_495,plain,(
    ! [A_320] :
      ( m1_pre_topc(A_320,'#skF_3')
      | ~ m1_pre_topc(A_320,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_485])).

tff(c_522,plain,(
    ! [A_322] :
      ( m1_pre_topc(A_322,'#skF_3')
      | ~ m1_pre_topc(A_322,'#skF_4')
      | ~ l1_pre_topc(A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_162,c_495])).

tff(c_211,plain,(
    ! [B_304,A_305] :
      ( m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(u1_struct_0(A_305)))
      | ~ m1_pre_topc(B_304,A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_220,plain,(
    ! [B_304] :
      ( m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_304,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_211])).

tff(c_248,plain,(
    ! [B_306] :
      ( m1_subset_1(u1_struct_0(B_306),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_306,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_220])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_265,plain,(
    ! [B_307] :
      ( r1_tarski(u1_struct_0(B_307),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_307,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_248,c_8])).

tff(c_273,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_265])).

tff(c_282,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_540,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_522,c_282])).

tff(c_561,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_540])).

tff(c_570,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_561])).

tff(c_574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_570])).

tff(c_575,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_226,plain,(
    ! [B_304] :
      ( m1_subset_1(u1_struct_0(B_304),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_304,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_211])).

tff(c_754,plain,(
    ! [B_334] :
      ( m1_subset_1(u1_struct_0(B_334),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_334,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_226])).

tff(c_911,plain,(
    ! [B_338] :
      ( r1_tarski(u1_struct_0(B_338),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_338,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_754,c_8])).

tff(c_916,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_911])).

tff(c_928,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_916])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_932,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_928,c_2])).

tff(c_935,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_932])).

tff(c_943,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_149])).

tff(c_54,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_52,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_88,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_1566,plain,(
    ! [C_361,A_359,G_364,D_360,E_363,B_362] :
      ( r1_tmap_1(D_360,B_362,E_363,G_364)
      | ~ r1_tmap_1(C_361,B_362,k3_tmap_1(A_359,B_362,D_360,C_361,E_363),G_364)
      | ~ m1_subset_1(G_364,u1_struct_0(C_361))
      | ~ m1_subset_1(G_364,u1_struct_0(D_360))
      | ~ m1_pre_topc(C_361,D_360)
      | ~ v1_tsep_1(C_361,D_360)
      | ~ m1_subset_1(E_363,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_360),u1_struct_0(B_362))))
      | ~ v1_funct_2(E_363,u1_struct_0(D_360),u1_struct_0(B_362))
      | ~ v1_funct_1(E_363)
      | ~ m1_pre_topc(D_360,A_359)
      | v2_struct_0(D_360)
      | ~ m1_pre_topc(C_361,A_359)
      | v2_struct_0(C_361)
      | ~ l1_pre_topc(B_362)
      | ~ v2_pre_topc(B_362)
      | v2_struct_0(B_362)
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_1568,plain,
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
    inference(resolution,[status(thm)],[c_88,c_1566])).

tff(c_1571,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_72,c_68,c_66,c_156,c_114,c_145,c_155,c_114,c_145,c_838,c_157,c_145,c_157,c_943,c_1568])).

tff(c_1572,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_74,c_70,c_50,c_1571])).

tff(c_194,plain,(
    ! [B_302,A_303] :
      ( v2_pre_topc(B_302)
      | ~ m1_pre_topc(B_302,A_303)
      | ~ l1_pre_topc(A_303)
      | ~ v2_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_200,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_194])).

tff(c_207,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_200])).

tff(c_24,plain,(
    ! [A_16] :
      ( v3_pre_topc(k2_struct_0(A_16),A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1087,plain,(
    ! [B_348,A_349] :
      ( v1_tsep_1(B_348,A_349)
      | ~ v3_pre_topc(u1_struct_0(B_348),A_349)
      | ~ m1_subset_1(u1_struct_0(B_348),k1_zfmisc_1(u1_struct_0(A_349)))
      | ~ m1_pre_topc(B_348,A_349)
      | ~ l1_pre_topc(A_349)
      | ~ v2_pre_topc(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2078,plain,(
    ! [B_381,A_382] :
      ( v1_tsep_1(B_381,A_382)
      | ~ v3_pre_topc(u1_struct_0(B_381),A_382)
      | ~ v2_pre_topc(A_382)
      | ~ m1_pre_topc(B_381,A_382)
      | ~ l1_pre_topc(A_382) ) ),
    inference(resolution,[status(thm)],[c_38,c_1087])).

tff(c_12575,plain,(
    ! [A_561] :
      ( v1_tsep_1('#skF_3',A_561)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_561)
      | ~ v2_pre_topc(A_561)
      | ~ m1_pre_topc('#skF_3',A_561)
      | ~ l1_pre_topc(A_561) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_2078])).

tff(c_12591,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_12575])).

tff(c_12602,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_138,c_838,c_12591])).

tff(c_12604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1572,c_12602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:39:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.75/3.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.75/3.57  
% 9.75/3.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.75/3.57  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.75/3.57  
% 9.75/3.57  %Foreground sorts:
% 9.75/3.57  
% 9.75/3.57  
% 9.75/3.57  %Background operators:
% 9.75/3.57  
% 9.75/3.57  
% 9.75/3.57  %Foreground operators:
% 9.75/3.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.75/3.57  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 9.75/3.57  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 9.75/3.57  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 9.75/3.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.75/3.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 9.75/3.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.75/3.57  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 9.75/3.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 9.75/3.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.75/3.57  tff('#skF_7', type, '#skF_7': $i).
% 9.75/3.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.75/3.57  tff('#skF_5', type, '#skF_5': $i).
% 9.75/3.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.75/3.57  tff('#skF_6', type, '#skF_6': $i).
% 9.75/3.57  tff('#skF_2', type, '#skF_2': $i).
% 9.75/3.57  tff('#skF_3', type, '#skF_3': $i).
% 9.75/3.57  tff('#skF_1', type, '#skF_1': $i).
% 9.75/3.57  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.75/3.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.75/3.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.75/3.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.75/3.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.75/3.57  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 9.75/3.57  tff('#skF_4', type, '#skF_4': $i).
% 9.75/3.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.75/3.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.75/3.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.75/3.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.75/3.57  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.75/3.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.75/3.57  
% 9.75/3.59  tff(f_251, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 9.75/3.59  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.75/3.59  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.75/3.59  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.75/3.59  tff(f_140, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.75/3.59  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 9.75/3.59  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 9.75/3.59  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.75/3.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.75/3.59  tff(f_202, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 9.75/3.59  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 9.75/3.59  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 9.75/3.59  tff(f_114, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 9.75/3.59  tff(c_86, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_50, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_84, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_82, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_72, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_125, plain, (![B_295, A_296]: (l1_pre_topc(B_295) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.75/3.59  tff(c_131, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_125])).
% 9.75/3.59  tff(c_138, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_131])).
% 9.75/3.59  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.75/3.59  tff(c_101, plain, (![A_291]: (u1_struct_0(A_291)=k2_struct_0(A_291) | ~l1_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.75/3.59  tff(c_105, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_16, c_101])).
% 9.75/3.59  tff(c_145, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_138, c_105])).
% 9.75/3.59  tff(c_106, plain, (![A_292]: (u1_struct_0(A_292)=k2_struct_0(A_292) | ~l1_pre_topc(A_292))), inference(resolution, [status(thm)], [c_16, c_101])).
% 9.75/3.59  tff(c_114, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_106])).
% 9.75/3.59  tff(c_64, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_119, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_64])).
% 9.75/3.59  tff(c_156, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_119])).
% 9.75/3.59  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_150, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_62])).
% 9.75/3.59  tff(c_155, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_150])).
% 9.75/3.59  tff(c_134, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_125])).
% 9.75/3.59  tff(c_141, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_134])).
% 9.75/3.59  tff(c_42, plain, (![A_33]: (m1_pre_topc(A_33, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.75/3.59  tff(c_149, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_141, c_105])).
% 9.75/3.59  tff(c_60, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_162, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_60])).
% 9.75/3.59  tff(c_771, plain, (![A_335, B_336]: (m1_pre_topc(A_335, g1_pre_topc(u1_struct_0(B_336), u1_pre_topc(B_336))) | ~m1_pre_topc(A_335, B_336) | ~l1_pre_topc(B_336) | ~l1_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.75/3.59  tff(c_789, plain, (![A_335]: (m1_pre_topc(A_335, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_335, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_335))), inference(superposition, [status(thm), theory('equality')], [c_149, c_771])).
% 9.75/3.59  tff(c_814, plain, (![A_337]: (m1_pre_topc(A_337, '#skF_4') | ~m1_pre_topc(A_337, '#skF_3') | ~l1_pre_topc(A_337))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_162, c_789])).
% 9.75/3.59  tff(c_828, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_814])).
% 9.75/3.59  tff(c_838, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_828])).
% 9.75/3.59  tff(c_58, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_157, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_58])).
% 9.75/3.59  tff(c_485, plain, (![A_320, B_321]: (m1_pre_topc(A_320, B_321) | ~m1_pre_topc(A_320, g1_pre_topc(u1_struct_0(B_321), u1_pre_topc(B_321))) | ~l1_pre_topc(B_321) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_68])).
% 9.75/3.59  tff(c_495, plain, (![A_320]: (m1_pre_topc(A_320, '#skF_3') | ~m1_pre_topc(A_320, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_320))), inference(superposition, [status(thm), theory('equality')], [c_149, c_485])).
% 9.75/3.59  tff(c_522, plain, (![A_322]: (m1_pre_topc(A_322, '#skF_3') | ~m1_pre_topc(A_322, '#skF_4') | ~l1_pre_topc(A_322))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_162, c_495])).
% 9.75/3.59  tff(c_211, plain, (![B_304, A_305]: (m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(u1_struct_0(A_305))) | ~m1_pre_topc(B_304, A_305) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.75/3.59  tff(c_220, plain, (![B_304]: (m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_304, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_211])).
% 9.75/3.59  tff(c_248, plain, (![B_306]: (m1_subset_1(u1_struct_0(B_306), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_306, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_220])).
% 9.75/3.59  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.75/3.59  tff(c_265, plain, (![B_307]: (r1_tarski(u1_struct_0(B_307), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_307, '#skF_3'))), inference(resolution, [status(thm)], [c_248, c_8])).
% 9.75/3.59  tff(c_273, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_265])).
% 9.75/3.59  tff(c_282, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_273])).
% 9.75/3.59  tff(c_540, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_522, c_282])).
% 9.75/3.59  tff(c_561, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_540])).
% 9.75/3.59  tff(c_570, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_561])).
% 9.75/3.59  tff(c_574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_570])).
% 9.75/3.59  tff(c_575, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_273])).
% 9.75/3.59  tff(c_226, plain, (![B_304]: (m1_subset_1(u1_struct_0(B_304), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_304, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_211])).
% 9.75/3.59  tff(c_754, plain, (![B_334]: (m1_subset_1(u1_struct_0(B_334), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_334, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_226])).
% 9.75/3.59  tff(c_911, plain, (![B_338]: (r1_tarski(u1_struct_0(B_338), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_338, '#skF_4'))), inference(resolution, [status(thm)], [c_754, c_8])).
% 9.75/3.59  tff(c_916, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_149, c_911])).
% 9.75/3.59  tff(c_928, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_838, c_916])).
% 9.75/3.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.75/3.59  tff(c_932, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_928, c_2])).
% 9.75/3.59  tff(c_935, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_575, c_932])).
% 9.75/3.59  tff(c_943, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_935, c_149])).
% 9.75/3.59  tff(c_54, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_52, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_251])).
% 9.75/3.59  tff(c_88, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 9.75/3.59  tff(c_1566, plain, (![C_361, A_359, G_364, D_360, E_363, B_362]: (r1_tmap_1(D_360, B_362, E_363, G_364) | ~r1_tmap_1(C_361, B_362, k3_tmap_1(A_359, B_362, D_360, C_361, E_363), G_364) | ~m1_subset_1(G_364, u1_struct_0(C_361)) | ~m1_subset_1(G_364, u1_struct_0(D_360)) | ~m1_pre_topc(C_361, D_360) | ~v1_tsep_1(C_361, D_360) | ~m1_subset_1(E_363, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_360), u1_struct_0(B_362)))) | ~v1_funct_2(E_363, u1_struct_0(D_360), u1_struct_0(B_362)) | ~v1_funct_1(E_363) | ~m1_pre_topc(D_360, A_359) | v2_struct_0(D_360) | ~m1_pre_topc(C_361, A_359) | v2_struct_0(C_361) | ~l1_pre_topc(B_362) | ~v2_pre_topc(B_362) | v2_struct_0(B_362) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(cnfTransformation, [status(thm)], [f_202])).
% 9.75/3.59  tff(c_1568, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_1566])).
% 9.75/3.59  tff(c_1571, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_72, c_68, c_66, c_156, c_114, c_145, c_155, c_114, c_145, c_838, c_157, c_145, c_157, c_943, c_1568])).
% 9.75/3.59  tff(c_1572, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_74, c_70, c_50, c_1571])).
% 9.75/3.59  tff(c_194, plain, (![B_302, A_303]: (v2_pre_topc(B_302) | ~m1_pre_topc(B_302, A_303) | ~l1_pre_topc(A_303) | ~v2_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.75/3.59  tff(c_200, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_194])).
% 9.75/3.59  tff(c_207, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_200])).
% 9.75/3.59  tff(c_24, plain, (![A_16]: (v3_pre_topc(k2_struct_0(A_16), A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.75/3.59  tff(c_38, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_121])).
% 9.75/3.59  tff(c_1087, plain, (![B_348, A_349]: (v1_tsep_1(B_348, A_349) | ~v3_pre_topc(u1_struct_0(B_348), A_349) | ~m1_subset_1(u1_struct_0(B_348), k1_zfmisc_1(u1_struct_0(A_349))) | ~m1_pre_topc(B_348, A_349) | ~l1_pre_topc(A_349) | ~v2_pre_topc(A_349))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.75/3.59  tff(c_2078, plain, (![B_381, A_382]: (v1_tsep_1(B_381, A_382) | ~v3_pre_topc(u1_struct_0(B_381), A_382) | ~v2_pre_topc(A_382) | ~m1_pre_topc(B_381, A_382) | ~l1_pre_topc(A_382))), inference(resolution, [status(thm)], [c_38, c_1087])).
% 9.75/3.59  tff(c_12575, plain, (![A_561]: (v1_tsep_1('#skF_3', A_561) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_561) | ~v2_pre_topc(A_561) | ~m1_pre_topc('#skF_3', A_561) | ~l1_pre_topc(A_561))), inference(superposition, [status(thm), theory('equality')], [c_943, c_2078])).
% 9.75/3.59  tff(c_12591, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_12575])).
% 9.75/3.59  tff(c_12602, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_138, c_838, c_12591])).
% 9.75/3.59  tff(c_12604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1572, c_12602])).
% 9.75/3.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.75/3.59  
% 9.75/3.59  Inference rules
% 9.75/3.59  ----------------------
% 9.75/3.59  #Ref     : 0
% 9.75/3.59  #Sup     : 2475
% 9.75/3.59  #Fact    : 0
% 9.75/3.59  #Define  : 0
% 9.75/3.59  #Split   : 39
% 9.75/3.59  #Chain   : 0
% 9.75/3.59  #Close   : 0
% 9.75/3.59  
% 9.75/3.59  Ordering : KBO
% 9.75/3.59  
% 9.75/3.59  Simplification rules
% 9.75/3.59  ----------------------
% 9.75/3.59  #Subsume      : 504
% 9.75/3.59  #Demod        : 4962
% 9.75/3.59  #Tautology    : 877
% 9.75/3.59  #SimpNegUnit  : 441
% 9.75/3.59  #BackRed      : 49
% 9.75/3.59  
% 9.75/3.59  #Partial instantiations: 0
% 9.75/3.59  #Strategies tried      : 1
% 9.75/3.59  
% 9.75/3.59  Timing (in seconds)
% 9.75/3.59  ----------------------
% 9.75/3.60  Preprocessing        : 0.59
% 9.75/3.60  Parsing              : 0.30
% 9.75/3.60  CNF conversion       : 0.07
% 9.75/3.60  Main loop            : 2.10
% 9.75/3.60  Inferencing          : 0.58
% 9.75/3.60  Reduction            : 0.90
% 9.75/3.60  Demodulation         : 0.70
% 9.75/3.60  BG Simplification    : 0.07
% 9.75/3.60  Subsumption          : 0.45
% 9.75/3.60  Abstraction          : 0.08
% 9.75/3.60  MUC search           : 0.00
% 9.75/3.60  Cooper               : 0.00
% 9.75/3.60  Total                : 2.73
% 9.75/3.60  Index Insertion      : 0.00
% 9.75/3.60  Index Deletion       : 0.00
% 9.75/3.60  Index Matching       : 0.00
% 9.75/3.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
