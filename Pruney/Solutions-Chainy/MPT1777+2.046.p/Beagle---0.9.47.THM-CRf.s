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
% DateTime   : Thu Dec  3 10:27:38 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  165 (5952 expanded)
%              Number of leaves         :   44 (2029 expanded)
%              Depth                    :   24
%              Number of atoms          :  385 (26718 expanded)
%              Number of equality atoms :   20 (2939 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_227,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_178,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_105,axiom,(
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

tff(c_86,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_50,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_84,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_82,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_72,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_125,plain,(
    ! [B_292,A_293] :
      ( l1_pre_topc(B_292)
      | ~ m1_pre_topc(B_292,A_293)
      | ~ l1_pre_topc(A_293) ) ),
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
    ! [A_288] :
      ( u1_struct_0(A_288) = k2_struct_0(A_288)
      | ~ l1_struct_0(A_288) ) ),
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
    ! [A_289] :
      ( u1_struct_0(A_289) = k2_struct_0(A_289)
      | ~ l1_pre_topc(A_289) ) ),
    inference(resolution,[status(thm)],[c_16,c_101])).

tff(c_114,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_106])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_119,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_64])).

tff(c_156,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_119])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

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
    ! [A_30] :
      ( m1_pre_topc(A_30,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_149,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_105])).

tff(c_60,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_162,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_60])).

tff(c_656,plain,(
    ! [A_326,B_327] :
      ( m1_pre_topc(A_326,g1_pre_topc(u1_struct_0(B_327),u1_pre_topc(B_327)))
      | ~ m1_pre_topc(A_326,B_327)
      | ~ l1_pre_topc(B_327)
      | ~ l1_pre_topc(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_667,plain,(
    ! [A_326] :
      ( m1_pre_topc(A_326,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_326,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_656])).

tff(c_688,plain,(
    ! [A_328] :
      ( m1_pre_topc(A_328,'#skF_4')
      | ~ m1_pre_topc(A_328,'#skF_3')
      | ~ l1_pre_topc(A_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_162,c_667])).

tff(c_699,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_688])).

tff(c_708,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_699])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_157,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_58])).

tff(c_372,plain,(
    ! [A_312,B_313] :
      ( m1_pre_topc(A_312,B_313)
      | ~ m1_pre_topc(A_312,g1_pre_topc(u1_struct_0(B_313),u1_pre_topc(B_313)))
      | ~ l1_pre_topc(B_313)
      | ~ l1_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_379,plain,(
    ! [A_312] :
      ( m1_pre_topc(A_312,'#skF_3')
      | ~ m1_pre_topc(A_312,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_372])).

tff(c_427,plain,(
    ! [A_315] :
      ( m1_pre_topc(A_315,'#skF_3')
      | ~ m1_pre_topc(A_315,'#skF_4')
      | ~ l1_pre_topc(A_315) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_162,c_379])).

tff(c_211,plain,(
    ! [B_301,A_302] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(u1_struct_0(A_302)))
      | ~ m1_pre_topc(B_301,A_302)
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_220,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_301,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_211])).

tff(c_248,plain,(
    ! [B_303] :
      ( m1_subset_1(u1_struct_0(B_303),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_303,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_220])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_265,plain,(
    ! [B_304] :
      ( r1_tarski(u1_struct_0(B_304),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_304,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_248,c_8])).

tff(c_273,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_265])).

tff(c_282,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_442,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_427,c_282])).

tff(c_462,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_442])).

tff(c_514,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_462])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_514])).

tff(c_519,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_226,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_301,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_211])).

tff(c_917,plain,(
    ! [B_336] :
      ( m1_subset_1(u1_struct_0(B_336),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_336,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_226])).

tff(c_923,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_917])).

tff(c_935,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_708,c_923])).

tff(c_941,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_935,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_943,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_941,c_2])).

tff(c_946,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_943])).

tff(c_956,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_149])).

tff(c_54,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_52,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_88,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_1911,plain,(
    ! [A_372,G_374,D_377,E_376,C_373,B_375] :
      ( r1_tmap_1(D_377,B_375,E_376,G_374)
      | ~ r1_tmap_1(C_373,B_375,k3_tmap_1(A_372,B_375,D_377,C_373,E_376),G_374)
      | ~ m1_subset_1(G_374,u1_struct_0(C_373))
      | ~ m1_subset_1(G_374,u1_struct_0(D_377))
      | ~ m1_pre_topc(C_373,D_377)
      | ~ v1_tsep_1(C_373,D_377)
      | ~ m1_subset_1(E_376,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_377),u1_struct_0(B_375))))
      | ~ v1_funct_2(E_376,u1_struct_0(D_377),u1_struct_0(B_375))
      | ~ v1_funct_1(E_376)
      | ~ m1_pre_topc(D_377,A_372)
      | v2_struct_0(D_377)
      | ~ m1_pre_topc(C_373,A_372)
      | v2_struct_0(C_373)
      | ~ l1_pre_topc(B_375)
      | ~ v2_pre_topc(B_375)
      | v2_struct_0(B_375)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1913,plain,
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
    inference(resolution,[status(thm)],[c_88,c_1911])).

tff(c_1916,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_78,c_76,c_72,c_68,c_66,c_156,c_114,c_145,c_155,c_114,c_145,c_708,c_157,c_145,c_157,c_956,c_1913])).

tff(c_1917,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_80,c_74,c_70,c_50,c_1916])).

tff(c_194,plain,(
    ! [B_299,A_300] :
      ( v2_pre_topc(B_299)
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_203,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_194])).

tff(c_210,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_203])).

tff(c_520,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_44,plain,(
    ! [C_37,A_31,B_35] :
      ( m1_pre_topc(C_37,A_31)
      | ~ m1_pre_topc(C_37,B_35)
      | ~ m1_pre_topc(B_35,A_31)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_717,plain,(
    ! [A_31] :
      ( m1_pre_topc('#skF_3',A_31)
      | ~ m1_pre_topc('#skF_4',A_31)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_708,c_44])).

tff(c_32,plain,(
    ! [A_19] :
      ( v3_pre_topc(k2_struct_0(A_19),A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_965,plain,
    ( v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_32])).

tff(c_969,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_141,c_965])).

tff(c_695,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_520,c_688])).

tff(c_705,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_695])).

tff(c_926,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_917])).

tff(c_937,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_926])).

tff(c_896,plain,(
    ! [B_334,A_335] :
      ( v3_pre_topc(B_334,g1_pre_topc(u1_struct_0(A_335),u1_pre_topc(A_335)))
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0(A_335)))
      | ~ v3_pre_topc(B_334,A_335)
      | ~ l1_pre_topc(A_335)
      | ~ v2_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_899,plain,(
    ! [B_334] :
      ( v3_pre_topc(B_334,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_334,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_334,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_896])).

tff(c_910,plain,(
    ! [B_334] :
      ( v3_pre_topc(B_334,'#skF_4')
      | ~ m1_subset_1(B_334,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_334,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_141,c_149,c_162,c_899])).

tff(c_1603,plain,(
    ! [B_359] :
      ( v3_pre_topc(B_359,'#skF_4')
      | ~ m1_subset_1(B_359,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_359,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_910])).

tff(c_1609,plain,
    ( v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_937,c_1603])).

tff(c_1620,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_969,c_1609])).

tff(c_241,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_301,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_220])).

tff(c_953,plain,(
    ! [B_301] :
      ( m1_subset_1(u1_struct_0(B_301),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_301,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_241])).

tff(c_954,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_162])).

tff(c_1395,plain,(
    ! [B_352,A_353] :
      ( v3_pre_topc(B_352,A_353)
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_353),u1_pre_topc(A_353)))))
      | ~ v3_pre_topc(B_352,g1_pre_topc(u1_struct_0(A_353),u1_pre_topc(A_353)))
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1405,plain,(
    ! [B_352] :
      ( v3_pre_topc(B_352,'#skF_3')
      | ~ m1_subset_1(B_352,k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))))
      | ~ v3_pre_topc(B_352,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_1395])).

tff(c_1725,plain,(
    ! [B_364] :
      ( v3_pre_topc(B_364,'#skF_3')
      | ~ m1_subset_1(B_364,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_364,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_141,c_954,c_956,c_145,c_954,c_1405])).

tff(c_1739,plain,(
    ! [B_301] :
      ( v3_pre_topc(u1_struct_0(B_301),'#skF_3')
      | ~ v3_pre_topc(u1_struct_0(B_301),'#skF_4')
      | ~ m1_pre_topc(B_301,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_953,c_1725])).

tff(c_40,plain,(
    ! [B_29,A_27] :
      ( m1_subset_1(u1_struct_0(B_29),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1025,plain,(
    ! [B_337,A_338] :
      ( v1_tsep_1(B_337,A_338)
      | ~ v3_pre_topc(u1_struct_0(B_337),A_338)
      | ~ m1_subset_1(u1_struct_0(B_337),k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ m1_pre_topc(B_337,A_338)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2469,plain,(
    ! [B_412,A_413] :
      ( v1_tsep_1(B_412,A_413)
      | ~ v3_pre_topc(u1_struct_0(B_412),A_413)
      | ~ v2_pre_topc(A_413)
      | ~ m1_pre_topc(B_412,A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(resolution,[status(thm)],[c_40,c_1025])).

tff(c_2478,plain,(
    ! [B_301] :
      ( v1_tsep_1(B_301,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v3_pre_topc(u1_struct_0(B_301),'#skF_4')
      | ~ m1_pre_topc(B_301,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1739,c_2469])).

tff(c_2509,plain,(
    ! [B_414] :
      ( v1_tsep_1(B_414,'#skF_3')
      | ~ v3_pre_topc(u1_struct_0(B_414),'#skF_4')
      | ~ m1_pre_topc(B_414,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_210,c_2478])).

tff(c_2519,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_956,c_2509])).

tff(c_2534,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_2519])).

tff(c_2537,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2534])).

tff(c_2545,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_717,c_2537])).

tff(c_2558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_141,c_520,c_2545])).

tff(c_2560,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2534])).

tff(c_2559,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2534])).

tff(c_200,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_194])).

tff(c_207,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_200])).

tff(c_1151,plain,(
    ! [B_341,A_342] :
      ( v3_pre_topc(u1_struct_0(B_341),A_342)
      | ~ v1_tsep_1(B_341,A_342)
      | ~ m1_subset_1(u1_struct_0(B_341),k1_zfmisc_1(u1_struct_0(A_342)))
      | ~ m1_pre_topc(B_341,A_342)
      | ~ l1_pre_topc(A_342)
      | ~ v2_pre_topc(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2331,plain,(
    ! [B_402,A_403] :
      ( v3_pre_topc(u1_struct_0(B_402),A_403)
      | ~ v1_tsep_1(B_402,A_403)
      | ~ v2_pre_topc(A_403)
      | ~ m1_pre_topc(B_402,A_403)
      | ~ l1_pre_topc(A_403) ) ),
    inference(resolution,[status(thm)],[c_40,c_1151])).

tff(c_1617,plain,(
    ! [B_301] :
      ( v3_pre_topc(u1_struct_0(B_301),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_301),'#skF_3')
      | ~ m1_pre_topc(B_301,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_953,c_1603])).

tff(c_2335,plain,(
    ! [B_402] :
      ( v3_pre_topc(u1_struct_0(B_402),'#skF_4')
      | ~ v1_tsep_1(B_402,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_402,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2331,c_1617])).

tff(c_2354,plain,(
    ! [B_402] :
      ( v3_pre_topc(u1_struct_0(B_402),'#skF_4')
      | ~ v1_tsep_1(B_402,'#skF_3')
      | ~ m1_pre_topc(B_402,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_210,c_2335])).

tff(c_2472,plain,(
    ! [B_402] :
      ( v1_tsep_1(B_402,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_402,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tsep_1(B_402,'#skF_3')
      | ~ m1_pre_topc(B_402,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2354,c_2469])).

tff(c_2603,plain,(
    ! [B_419] :
      ( v1_tsep_1(B_419,'#skF_4')
      | ~ m1_pre_topc(B_419,'#skF_4')
      | ~ v1_tsep_1(B_419,'#skF_3')
      | ~ m1_pre_topc(B_419,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_207,c_2472])).

tff(c_2606,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2559,c_2603])).

tff(c_2612,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_708,c_2606])).

tff(c_2614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1917,c_2612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n003.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 17:16:27 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.87  
% 4.60/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.87  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.60/1.87  
% 4.60/1.87  %Foreground sorts:
% 4.60/1.87  
% 4.60/1.87  
% 4.60/1.87  %Background operators:
% 4.60/1.87  
% 4.60/1.87  
% 4.60/1.87  %Foreground operators:
% 4.60/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.60/1.87  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.60/1.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.60/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.87  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.60/1.87  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.60/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.60/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.60/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.60/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.60/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.87  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.60/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.60/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.60/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.60/1.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.60/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.87  
% 4.60/1.90  tff(f_227, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.60/1.90  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.60/1.90  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.60/1.90  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.60/1.90  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.60/1.90  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.60/1.90  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.60/1.90  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.60/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.60/1.90  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.60/1.90  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.60/1.90  tff(f_128, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 4.60/1.90  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.60/1.90  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 4.60/1.90  tff(f_105, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.60/1.90  tff(c_86, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_50, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_84, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_82, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_72, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_125, plain, (![B_292, A_293]: (l1_pre_topc(B_292) | ~m1_pre_topc(B_292, A_293) | ~l1_pre_topc(A_293))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.60/1.90  tff(c_131, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_125])).
% 4.60/1.90  tff(c_138, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_131])).
% 4.60/1.90  tff(c_16, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.60/1.90  tff(c_101, plain, (![A_288]: (u1_struct_0(A_288)=k2_struct_0(A_288) | ~l1_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.60/1.90  tff(c_105, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_16, c_101])).
% 4.60/1.90  tff(c_145, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_138, c_105])).
% 4.60/1.90  tff(c_106, plain, (![A_289]: (u1_struct_0(A_289)=k2_struct_0(A_289) | ~l1_pre_topc(A_289))), inference(resolution, [status(thm)], [c_16, c_101])).
% 4.60/1.90  tff(c_114, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_106])).
% 4.60/1.90  tff(c_64, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_119, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_64])).
% 4.60/1.90  tff(c_156, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_119])).
% 4.60/1.90  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_150, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_62])).
% 4.60/1.90  tff(c_155, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_150])).
% 4.60/1.90  tff(c_134, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_125])).
% 4.60/1.90  tff(c_141, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_134])).
% 4.60/1.90  tff(c_42, plain, (![A_30]: (m1_pre_topc(A_30, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.60/1.90  tff(c_149, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_141, c_105])).
% 4.60/1.90  tff(c_60, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_162, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_60])).
% 4.60/1.90  tff(c_656, plain, (![A_326, B_327]: (m1_pre_topc(A_326, g1_pre_topc(u1_struct_0(B_327), u1_pre_topc(B_327))) | ~m1_pre_topc(A_326, B_327) | ~l1_pre_topc(B_327) | ~l1_pre_topc(A_326))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.60/1.90  tff(c_667, plain, (![A_326]: (m1_pre_topc(A_326, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_326, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_326))), inference(superposition, [status(thm), theory('equality')], [c_149, c_656])).
% 4.60/1.90  tff(c_688, plain, (![A_328]: (m1_pre_topc(A_328, '#skF_4') | ~m1_pre_topc(A_328, '#skF_3') | ~l1_pre_topc(A_328))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_162, c_667])).
% 4.60/1.90  tff(c_699, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_42, c_688])).
% 4.60/1.90  tff(c_708, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_699])).
% 4.60/1.90  tff(c_58, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_157, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_58])).
% 4.60/1.90  tff(c_372, plain, (![A_312, B_313]: (m1_pre_topc(A_312, B_313) | ~m1_pre_topc(A_312, g1_pre_topc(u1_struct_0(B_313), u1_pre_topc(B_313))) | ~l1_pre_topc(B_313) | ~l1_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.60/1.90  tff(c_379, plain, (![A_312]: (m1_pre_topc(A_312, '#skF_3') | ~m1_pre_topc(A_312, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_312))), inference(superposition, [status(thm), theory('equality')], [c_149, c_372])).
% 4.60/1.90  tff(c_427, plain, (![A_315]: (m1_pre_topc(A_315, '#skF_3') | ~m1_pre_topc(A_315, '#skF_4') | ~l1_pre_topc(A_315))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_162, c_379])).
% 4.60/1.90  tff(c_211, plain, (![B_301, A_302]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(u1_struct_0(A_302))) | ~m1_pre_topc(B_301, A_302) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.90  tff(c_220, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_301, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_211])).
% 4.60/1.90  tff(c_248, plain, (![B_303]: (m1_subset_1(u1_struct_0(B_303), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_303, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_220])).
% 4.60/1.90  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.90  tff(c_265, plain, (![B_304]: (r1_tarski(u1_struct_0(B_304), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_304, '#skF_3'))), inference(resolution, [status(thm)], [c_248, c_8])).
% 4.60/1.90  tff(c_273, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_145, c_265])).
% 4.60/1.90  tff(c_282, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_273])).
% 4.60/1.90  tff(c_442, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_427, c_282])).
% 4.60/1.90  tff(c_462, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_442])).
% 4.60/1.90  tff(c_514, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_462])).
% 4.60/1.90  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_514])).
% 4.60/1.90  tff(c_519, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_273])).
% 4.60/1.90  tff(c_226, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_301, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_211])).
% 4.60/1.90  tff(c_917, plain, (![B_336]: (m1_subset_1(u1_struct_0(B_336), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_336, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_226])).
% 4.60/1.90  tff(c_923, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_149, c_917])).
% 4.60/1.90  tff(c_935, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_708, c_923])).
% 4.60/1.90  tff(c_941, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_935, c_8])).
% 4.60/1.90  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.90  tff(c_943, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_941, c_2])).
% 4.60/1.90  tff(c_946, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_943])).
% 4.60/1.90  tff(c_956, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_946, c_149])).
% 4.60/1.90  tff(c_54, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_52, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 4.60/1.90  tff(c_88, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 4.60/1.90  tff(c_1911, plain, (![A_372, G_374, D_377, E_376, C_373, B_375]: (r1_tmap_1(D_377, B_375, E_376, G_374) | ~r1_tmap_1(C_373, B_375, k3_tmap_1(A_372, B_375, D_377, C_373, E_376), G_374) | ~m1_subset_1(G_374, u1_struct_0(C_373)) | ~m1_subset_1(G_374, u1_struct_0(D_377)) | ~m1_pre_topc(C_373, D_377) | ~v1_tsep_1(C_373, D_377) | ~m1_subset_1(E_376, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_377), u1_struct_0(B_375)))) | ~v1_funct_2(E_376, u1_struct_0(D_377), u1_struct_0(B_375)) | ~v1_funct_1(E_376) | ~m1_pre_topc(D_377, A_372) | v2_struct_0(D_377) | ~m1_pre_topc(C_373, A_372) | v2_struct_0(C_373) | ~l1_pre_topc(B_375) | ~v2_pre_topc(B_375) | v2_struct_0(B_375) | ~l1_pre_topc(A_372) | ~v2_pre_topc(A_372) | v2_struct_0(A_372))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.60/1.90  tff(c_1913, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_88, c_1911])).
% 4.60/1.90  tff(c_1916, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_78, c_76, c_72, c_68, c_66, c_156, c_114, c_145, c_155, c_114, c_145, c_708, c_157, c_145, c_157, c_956, c_1913])).
% 4.60/1.90  tff(c_1917, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_86, c_80, c_74, c_70, c_50, c_1916])).
% 4.60/1.90  tff(c_194, plain, (![B_299, A_300]: (v2_pre_topc(B_299) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.60/1.90  tff(c_203, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_194])).
% 4.60/1.90  tff(c_210, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_203])).
% 4.60/1.90  tff(c_520, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_273])).
% 4.60/1.90  tff(c_44, plain, (![C_37, A_31, B_35]: (m1_pre_topc(C_37, A_31) | ~m1_pre_topc(C_37, B_35) | ~m1_pre_topc(B_35, A_31) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.60/1.90  tff(c_717, plain, (![A_31]: (m1_pre_topc('#skF_3', A_31) | ~m1_pre_topc('#skF_4', A_31) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(resolution, [status(thm)], [c_708, c_44])).
% 4.60/1.90  tff(c_32, plain, (![A_19]: (v3_pre_topc(k2_struct_0(A_19), A_19) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.60/1.90  tff(c_965, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_946, c_32])).
% 4.60/1.90  tff(c_969, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_141, c_965])).
% 4.60/1.90  tff(c_695, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_520, c_688])).
% 4.60/1.90  tff(c_705, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_695])).
% 4.60/1.90  tff(c_926, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_145, c_917])).
% 4.60/1.90  tff(c_937, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_705, c_926])).
% 4.60/1.90  tff(c_896, plain, (![B_334, A_335]: (v3_pre_topc(B_334, g1_pre_topc(u1_struct_0(A_335), u1_pre_topc(A_335))) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0(A_335))) | ~v3_pre_topc(B_334, A_335) | ~l1_pre_topc(A_335) | ~v2_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.90  tff(c_899, plain, (![B_334]: (v3_pre_topc(B_334, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(B_334, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_334, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_149, c_896])).
% 4.60/1.90  tff(c_910, plain, (![B_334]: (v3_pre_topc(B_334, '#skF_4') | ~m1_subset_1(B_334, k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~v3_pre_topc(B_334, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_141, c_149, c_162, c_899])).
% 4.60/1.90  tff(c_1603, plain, (![B_359]: (v3_pre_topc(B_359, '#skF_4') | ~m1_subset_1(B_359, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v3_pre_topc(B_359, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_946, c_910])).
% 4.60/1.90  tff(c_1609, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_937, c_1603])).
% 4.60/1.90  tff(c_1620, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_969, c_1609])).
% 4.60/1.90  tff(c_241, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_301, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_220])).
% 4.60/1.90  tff(c_953, plain, (![B_301]: (m1_subset_1(u1_struct_0(B_301), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_301, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_946, c_241])).
% 4.60/1.90  tff(c_954, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_946, c_162])).
% 4.60/1.90  tff(c_1395, plain, (![B_352, A_353]: (v3_pre_topc(B_352, A_353) | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_353), u1_pre_topc(A_353))))) | ~v3_pre_topc(B_352, g1_pre_topc(u1_struct_0(A_353), u1_pre_topc(A_353))) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.60/1.90  tff(c_1405, plain, (![B_352]: (v3_pre_topc(B_352, '#skF_3') | ~m1_subset_1(B_352, k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))))) | ~v3_pre_topc(B_352, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_956, c_1395])).
% 4.60/1.90  tff(c_1725, plain, (![B_364]: (v3_pre_topc(B_364, '#skF_3') | ~m1_subset_1(B_364, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v3_pre_topc(B_364, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_141, c_954, c_956, c_145, c_954, c_1405])).
% 4.60/1.90  tff(c_1739, plain, (![B_301]: (v3_pre_topc(u1_struct_0(B_301), '#skF_3') | ~v3_pre_topc(u1_struct_0(B_301), '#skF_4') | ~m1_pre_topc(B_301, '#skF_3'))), inference(resolution, [status(thm)], [c_953, c_1725])).
% 4.60/1.90  tff(c_40, plain, (![B_29, A_27]: (m1_subset_1(u1_struct_0(B_29), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_pre_topc(B_29, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.90  tff(c_1025, plain, (![B_337, A_338]: (v1_tsep_1(B_337, A_338) | ~v3_pre_topc(u1_struct_0(B_337), A_338) | ~m1_subset_1(u1_struct_0(B_337), k1_zfmisc_1(u1_struct_0(A_338))) | ~m1_pre_topc(B_337, A_338) | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.60/1.90  tff(c_2469, plain, (![B_412, A_413]: (v1_tsep_1(B_412, A_413) | ~v3_pre_topc(u1_struct_0(B_412), A_413) | ~v2_pre_topc(A_413) | ~m1_pre_topc(B_412, A_413) | ~l1_pre_topc(A_413))), inference(resolution, [status(thm)], [c_40, c_1025])).
% 4.60/1.90  tff(c_2478, plain, (![B_301]: (v1_tsep_1(B_301, '#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3') | ~v3_pre_topc(u1_struct_0(B_301), '#skF_4') | ~m1_pre_topc(B_301, '#skF_3'))), inference(resolution, [status(thm)], [c_1739, c_2469])).
% 4.60/1.90  tff(c_2509, plain, (![B_414]: (v1_tsep_1(B_414, '#skF_3') | ~v3_pre_topc(u1_struct_0(B_414), '#skF_4') | ~m1_pre_topc(B_414, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_210, c_2478])).
% 4.60/1.90  tff(c_2519, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_956, c_2509])).
% 4.60/1.90  tff(c_2534, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_2519])).
% 4.60/1.90  tff(c_2537, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_2534])).
% 4.60/1.90  tff(c_2545, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_717, c_2537])).
% 4.60/1.90  tff(c_2558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_141, c_520, c_2545])).
% 4.60/1.90  tff(c_2560, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_2534])).
% 4.60/1.90  tff(c_2559, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_2534])).
% 4.60/1.90  tff(c_200, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_194])).
% 4.60/1.90  tff(c_207, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_200])).
% 4.60/1.90  tff(c_1151, plain, (![B_341, A_342]: (v3_pre_topc(u1_struct_0(B_341), A_342) | ~v1_tsep_1(B_341, A_342) | ~m1_subset_1(u1_struct_0(B_341), k1_zfmisc_1(u1_struct_0(A_342))) | ~m1_pre_topc(B_341, A_342) | ~l1_pre_topc(A_342) | ~v2_pre_topc(A_342))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.60/1.90  tff(c_2331, plain, (![B_402, A_403]: (v3_pre_topc(u1_struct_0(B_402), A_403) | ~v1_tsep_1(B_402, A_403) | ~v2_pre_topc(A_403) | ~m1_pre_topc(B_402, A_403) | ~l1_pre_topc(A_403))), inference(resolution, [status(thm)], [c_40, c_1151])).
% 4.60/1.90  tff(c_1617, plain, (![B_301]: (v3_pre_topc(u1_struct_0(B_301), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_301), '#skF_3') | ~m1_pre_topc(B_301, '#skF_3'))), inference(resolution, [status(thm)], [c_953, c_1603])).
% 4.60/1.90  tff(c_2335, plain, (![B_402]: (v3_pre_topc(u1_struct_0(B_402), '#skF_4') | ~v1_tsep_1(B_402, '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc(B_402, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_2331, c_1617])).
% 4.60/1.90  tff(c_2354, plain, (![B_402]: (v3_pre_topc(u1_struct_0(B_402), '#skF_4') | ~v1_tsep_1(B_402, '#skF_3') | ~m1_pre_topc(B_402, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_210, c_2335])).
% 4.60/1.90  tff(c_2472, plain, (![B_402]: (v1_tsep_1(B_402, '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc(B_402, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tsep_1(B_402, '#skF_3') | ~m1_pre_topc(B_402, '#skF_3'))), inference(resolution, [status(thm)], [c_2354, c_2469])).
% 4.60/1.90  tff(c_2603, plain, (![B_419]: (v1_tsep_1(B_419, '#skF_4') | ~m1_pre_topc(B_419, '#skF_4') | ~v1_tsep_1(B_419, '#skF_3') | ~m1_pre_topc(B_419, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_138, c_207, c_2472])).
% 4.60/1.90  tff(c_2606, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2559, c_2603])).
% 4.60/1.90  tff(c_2612, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_708, c_2606])).
% 4.60/1.90  tff(c_2614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1917, c_2612])).
% 4.60/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.60/1.90  
% 4.60/1.90  Inference rules
% 4.60/1.90  ----------------------
% 4.60/1.90  #Ref     : 0
% 4.60/1.90  #Sup     : 522
% 4.60/1.90  #Fact    : 0
% 4.60/1.90  #Define  : 0
% 4.60/1.90  #Split   : 15
% 4.60/1.90  #Chain   : 0
% 4.60/1.90  #Close   : 0
% 4.60/1.90  
% 4.60/1.90  Ordering : KBO
% 4.60/1.90  
% 4.60/1.90  Simplification rules
% 4.60/1.90  ----------------------
% 4.60/1.90  #Subsume      : 111
% 4.60/1.90  #Demod        : 697
% 4.60/1.90  #Tautology    : 175
% 4.60/1.90  #SimpNegUnit  : 20
% 4.60/1.90  #BackRed      : 16
% 4.60/1.90  
% 4.60/1.90  #Partial instantiations: 0
% 4.60/1.90  #Strategies tried      : 1
% 4.60/1.90  
% 4.60/1.90  Timing (in seconds)
% 4.60/1.90  ----------------------
% 4.60/1.90  Preprocessing        : 0.39
% 4.60/1.91  Parsing              : 0.18
% 4.60/1.91  CNF conversion       : 0.05
% 4.60/1.91  Main loop            : 0.71
% 4.60/1.91  Inferencing          : 0.22
% 4.60/1.91  Reduction            : 0.26
% 4.60/1.91  Demodulation         : 0.19
% 4.60/1.91  BG Simplification    : 0.03
% 4.60/1.91  Subsumption          : 0.15
% 4.60/1.91  Abstraction          : 0.03
% 4.60/1.91  MUC search           : 0.00
% 4.60/1.91  Cooper               : 0.00
% 4.60/1.91  Total                : 1.16
% 4.60/1.91  Index Insertion      : 0.00
% 4.60/1.91  Index Deletion       : 0.00
% 4.60/1.91  Index Matching       : 0.00
% 4.60/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
