%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:37 EST 2020

% Result     : Theorem 12.13s
% Output     : CNFRefutation 12.13s
% Verified   : 
% Statistics : Number of formulae       :  149 (2522 expanded)
%              Number of leaves         :   44 ( 883 expanded)
%              Depth                    :   21
%              Number of atoms          :  405 (11978 expanded)
%              Number of equality atoms :   39 (1391 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_138,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_120,axiom,(
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
                & m1_pre_topc(C,B) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                     => ( ( v1_tsep_1(C,B)
                          & m1_pre_topc(C,B)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,A,E,F)
                                  <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_116,plain,(
    ! [B_319,A_320] :
      ( l1_pre_topc(B_319)
      | ~ m1_pre_topc(B_319,A_320)
      | ~ l1_pre_topc(A_320) ) ),
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
    ! [A_317] :
      ( u1_struct_0(A_317) = k2_struct_0(A_317)
      | ~ l1_struct_0(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_89])).

tff(c_140,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_93])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_150,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_50])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_167,plain,(
    ! [B_324,A_325] :
      ( v2_pre_topc(B_324)
      | ~ m1_pre_topc(B_324,A_325)
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_176,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_167])).

tff(c_183,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_176])).

tff(c_32,plain,(
    ! [A_56] :
      ( m1_pre_topc(A_56,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

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

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_141,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_52])).

tff(c_451,plain,(
    ! [A_342,B_343] :
      ( m1_pre_topc(A_342,B_343)
      | ~ m1_pre_topc(A_342,g1_pre_topc(u1_struct_0(B_343),u1_pre_topc(B_343)))
      | ~ l1_pre_topc(B_343)
      | ~ l1_pre_topc(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_464,plain,(
    ! [A_342] :
      ( m1_pre_topc(A_342,'#skF_3')
      | ~ m1_pre_topc(A_342,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_342) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_451])).

tff(c_488,plain,(
    ! [A_344] :
      ( m1_pre_topc(A_344,'#skF_3')
      | ~ m1_pre_topc(A_344,'#skF_4')
      | ~ l1_pre_topc(A_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_141,c_464])).

tff(c_184,plain,(
    ! [B_326,A_327] :
      ( r1_tarski(u1_struct_0(B_326),u1_struct_0(A_327))
      | ~ m1_pre_topc(B_326,A_327)
      | ~ l1_pre_topc(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_198,plain,(
    ! [B_326] :
      ( r1_tarski(u1_struct_0(B_326),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_326,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_184])).

tff(c_315,plain,(
    ! [B_333] :
      ( r1_tarski(u1_struct_0(B_333),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_333,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_198])).

tff(c_320,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_315])).

tff(c_429,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_491,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_488,c_429])).

tff(c_515,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_491])).

tff(c_536,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_515])).

tff(c_540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_536])).

tff(c_542,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_367,plain,(
    ! [A_338,B_339] :
      ( m1_pre_topc(A_338,g1_pre_topc(u1_struct_0(B_339),u1_pre_topc(B_339)))
      | ~ m1_pre_topc(A_338,B_339)
      | ~ l1_pre_topc(B_339)
      | ~ l1_pre_topc(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_381,plain,(
    ! [A_338] :
      ( m1_pre_topc(A_338,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_338,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_367])).

tff(c_394,plain,(
    ! [A_338] :
      ( m1_pre_topc(A_338,'#skF_4')
      | ~ m1_pre_topc(A_338,'#skF_3')
      | ~ l1_pre_topc(A_338) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_141,c_381])).

tff(c_545,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_542,c_394])).

tff(c_556,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_545])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_98,plain,(
    ! [A_318] :
      ( u1_struct_0(A_318) = k2_struct_0(A_318)
      | ~ l1_pre_topc(A_318) ) ),
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

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_1051,plain,(
    ! [C_364,B_363,D_362,E_361,A_365] :
      ( k3_tmap_1(A_365,B_363,C_364,D_362,E_361) = k2_partfun1(u1_struct_0(C_364),u1_struct_0(B_363),E_361,u1_struct_0(D_362))
      | ~ m1_pre_topc(D_362,C_364)
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364),u1_struct_0(B_363))))
      | ~ v1_funct_2(E_361,u1_struct_0(C_364),u1_struct_0(B_363))
      | ~ v1_funct_1(E_361)
      | ~ m1_pre_topc(D_362,A_365)
      | ~ m1_pre_topc(C_364,A_365)
      | ~ l1_pre_topc(B_363)
      | ~ v2_pre_topc(B_363)
      | v2_struct_0(B_363)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1057,plain,(
    ! [A_365,B_363,D_362,E_361] :
      ( k3_tmap_1(A_365,B_363,'#skF_4',D_362,E_361) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_363),E_361,u1_struct_0(D_362))
      | ~ m1_pre_topc(D_362,'#skF_4')
      | ~ m1_subset_1(E_361,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_363))))
      | ~ v1_funct_2(E_361,u1_struct_0('#skF_4'),u1_struct_0(B_363))
      | ~ v1_funct_1(E_361)
      | ~ m1_pre_topc(D_362,A_365)
      | ~ m1_pre_topc('#skF_4',A_365)
      | ~ l1_pre_topc(B_363)
      | ~ v2_pre_topc(B_363)
      | v2_struct_0(B_363)
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | v2_struct_0(A_365) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_1051])).

tff(c_13714,plain,(
    ! [A_760,B_761,D_762,E_763] :
      ( k3_tmap_1(A_760,B_761,'#skF_4',D_762,E_763) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_761),E_763,u1_struct_0(D_762))
      | ~ m1_pre_topc(D_762,'#skF_4')
      | ~ m1_subset_1(E_763,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_761))))
      | ~ v1_funct_2(E_763,k2_struct_0('#skF_4'),u1_struct_0(B_761))
      | ~ v1_funct_1(E_763)
      | ~ m1_pre_topc(D_762,A_760)
      | ~ m1_pre_topc('#skF_4',A_760)
      | ~ l1_pre_topc(B_761)
      | ~ v2_pre_topc(B_761)
      | v2_struct_0(B_761)
      | ~ l1_pre_topc(A_760)
      | ~ v2_pre_topc(A_760)
      | v2_struct_0(A_760) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_140,c_1057])).

tff(c_13720,plain,(
    ! [A_760,D_762,E_763] :
      ( k3_tmap_1(A_760,'#skF_2','#skF_4',D_762,E_763) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),E_763,u1_struct_0(D_762))
      | ~ m1_pre_topc(D_762,'#skF_4')
      | ~ m1_subset_1(E_763,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_763,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_763)
      | ~ m1_pre_topc(D_762,A_760)
      | ~ m1_pre_topc('#skF_4',A_760)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_760)
      | ~ v2_pre_topc(A_760)
      | v2_struct_0(A_760) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_13714])).

tff(c_13730,plain,(
    ! [A_760,D_762,E_763] :
      ( k3_tmap_1(A_760,'#skF_2','#skF_4',D_762,E_763) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_763,u1_struct_0(D_762))
      | ~ m1_pre_topc(D_762,'#skF_4')
      | ~ m1_subset_1(E_763,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_763,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_763)
      | ~ m1_pre_topc(D_762,A_760)
      | ~ m1_pre_topc('#skF_4',A_760)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_760)
      | ~ v2_pre_topc(A_760)
      | v2_struct_0(A_760) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_106,c_106,c_13720])).

tff(c_13903,plain,(
    ! [A_766,D_767,E_768] :
      ( k3_tmap_1(A_766,'#skF_2','#skF_4',D_767,E_768) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_768,u1_struct_0(D_767))
      | ~ m1_pre_topc(D_767,'#skF_4')
      | ~ m1_subset_1(E_768,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_768,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_768)
      | ~ m1_pre_topc(D_767,A_766)
      | ~ m1_pre_topc('#skF_4',A_766)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_13730])).

tff(c_13905,plain,(
    ! [A_766,D_767] :
      ( k3_tmap_1(A_766,'#skF_2','#skF_4',D_767,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_767))
      | ~ m1_pre_topc(D_767,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_767,A_766)
      | ~ m1_pre_topc('#skF_4',A_766)
      | ~ l1_pre_topc(A_766)
      | ~ v2_pre_topc(A_766)
      | v2_struct_0(A_766) ) ),
    inference(resolution,[status(thm)],[c_148,c_13903])).

tff(c_19176,plain,(
    ! [A_883,D_884] :
      ( k3_tmap_1(A_883,'#skF_2','#skF_4',D_884,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_884))
      | ~ m1_pre_topc(D_884,'#skF_4')
      | ~ m1_pre_topc(D_884,A_883)
      | ~ m1_pre_topc('#skF_4',A_883)
      | ~ l1_pre_topc(A_883)
      | ~ v2_pre_topc(A_883)
      | v2_struct_0(A_883) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_149,c_13905])).

tff(c_19254,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_556,c_19176])).

tff(c_19362,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_132,c_556,c_140,c_19254])).

tff(c_19363,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_19362])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_399,plain,(
    ! [A_340] :
      ( m1_pre_topc(A_340,'#skF_4')
      | ~ m1_pre_topc(A_340,'#skF_3')
      | ~ l1_pre_topc(A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_141,c_381])).

tff(c_407,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_399])).

tff(c_413,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_407])).

tff(c_541,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_192,plain,(
    ! [B_326] :
      ( r1_tarski(u1_struct_0(B_326),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_326,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_184])).

tff(c_220,plain,(
    ! [B_328] :
      ( r1_tarski(u1_struct_0(B_328),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_328,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_192])).

tff(c_228,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_220])).

tff(c_702,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_228])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_704,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_702,c_2])).

tff(c_707,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_704])).

tff(c_738,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_136])).

tff(c_19266,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_19176])).

tff(c_19379,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_60,c_413,c_738,c_19266])).

tff(c_19380,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_19379])).

tff(c_19409,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19363,c_19380])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_19410,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19409,c_80])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_20,plain,(
    ! [A_14] :
      ( v3_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [B_55,A_53] :
      ( m1_subset_1(u1_struct_0(B_55),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ m1_pre_topc(B_55,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_952,plain,(
    ! [B_359,A_360] :
      ( v1_tsep_1(B_359,A_360)
      | ~ v3_pre_topc(u1_struct_0(B_359),A_360)
      | ~ m1_subset_1(u1_struct_0(B_359),k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ m1_pre_topc(B_359,A_360)
      | ~ l1_pre_topc(A_360)
      | ~ v2_pre_topc(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1906,plain,(
    ! [B_427,A_428] :
      ( v1_tsep_1(B_427,A_428)
      | ~ v3_pre_topc(u1_struct_0(B_427),A_428)
      | ~ v2_pre_topc(A_428)
      | ~ m1_pre_topc(B_427,A_428)
      | ~ l1_pre_topc(A_428) ) ),
    inference(resolution,[status(thm)],[c_30,c_952])).

tff(c_2317,plain,(
    ! [A_457] :
      ( v1_tsep_1('#skF_3',A_457)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_457)
      | ~ v2_pre_topc(A_457)
      | ~ m1_pre_topc('#skF_3',A_457)
      | ~ l1_pre_topc(A_457) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_738,c_1906])).

tff(c_2327,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_2317])).

tff(c_2334,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_132,c_413,c_2327])).

tff(c_19258,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_413,c_19176])).

tff(c_19370,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_132,c_556,c_413,c_738,c_19258])).

tff(c_19371,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_19370])).

tff(c_19399,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19363,c_19371])).

tff(c_38,plain,(
    ! [D_179,C_163,B_131,A_67,G_193,E_187] :
      ( r1_tmap_1(D_179,A_67,E_187,G_193)
      | ~ r1_tmap_1(C_163,A_67,k3_tmap_1(B_131,A_67,D_179,C_163,E_187),G_193)
      | ~ m1_subset_1(G_193,u1_struct_0(C_163))
      | ~ m1_subset_1(G_193,u1_struct_0(D_179))
      | ~ m1_pre_topc(C_163,D_179)
      | ~ v1_tsep_1(C_163,B_131)
      | ~ m1_subset_1(E_187,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179),u1_struct_0(A_67))))
      | ~ v1_funct_2(E_187,u1_struct_0(D_179),u1_struct_0(A_67))
      | ~ v1_funct_1(E_187)
      | ~ m1_pre_topc(D_179,B_131)
      | v2_struct_0(D_179)
      | ~ m1_pre_topc(C_163,B_131)
      | v2_struct_0(C_163)
      | ~ l1_pre_topc(B_131)
      | ~ v2_pre_topc(B_131)
      | v2_struct_0(B_131)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_19402,plain,(
    ! [G_193] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',G_193)
      | ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5'),G_193)
      | ~ m1_subset_1(G_193,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_193,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ v1_tsep_1('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19399,c_38])).

tff(c_19406,plain,(
    ! [G_193] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',G_193)
      | ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5'),G_193)
      | ~ m1_subset_1(G_193,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_183,c_132,c_413,c_556,c_58,c_149,c_106,c_140,c_148,c_106,c_140,c_2334,c_413,c_140,c_738,c_19402])).

tff(c_19629,plain,(
    ! [G_890] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',G_890)
      | ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_4','#skF_5'),G_890)
      | ~ m1_subset_1(G_890,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_66,c_19406])).

tff(c_19632,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_19410,c_19629])).

tff(c_19635,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_19632])).

tff(c_19637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_19635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:17:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.13/5.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.13/5.15  
% 12.13/5.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.13/5.15  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.13/5.15  
% 12.13/5.15  %Foreground sorts:
% 12.13/5.15  
% 12.13/5.15  
% 12.13/5.15  %Background operators:
% 12.13/5.15  
% 12.13/5.15  
% 12.13/5.15  %Foreground operators:
% 12.13/5.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.13/5.15  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 12.13/5.15  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 12.13/5.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.13/5.15  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 12.13/5.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.13/5.15  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 12.13/5.15  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 12.13/5.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.13/5.15  tff('#skF_7', type, '#skF_7': $i).
% 12.13/5.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.13/5.15  tff('#skF_5', type, '#skF_5': $i).
% 12.13/5.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.13/5.15  tff('#skF_6', type, '#skF_6': $i).
% 12.13/5.15  tff('#skF_2', type, '#skF_2': $i).
% 12.13/5.15  tff('#skF_3', type, '#skF_3': $i).
% 12.13/5.15  tff('#skF_1', type, '#skF_1': $i).
% 12.13/5.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.13/5.15  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 12.13/5.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.13/5.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.13/5.15  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 12.13/5.15  tff('#skF_4', type, '#skF_4': $i).
% 12.13/5.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.13/5.15  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.13/5.15  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.13/5.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.13/5.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.13/5.15  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 12.13/5.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.13/5.15  
% 12.13/5.17  tff(f_251, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 12.13/5.17  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.13/5.17  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 12.13/5.17  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 12.13/5.17  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 12.13/5.17  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 12.13/5.17  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 12.13/5.17  tff(f_138, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 12.13/5.17  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 12.13/5.17  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.13/5.17  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 12.13/5.17  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 12.13/5.17  tff(f_120, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 12.13/5.17  tff(f_202, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 12.13/5.17  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_116, plain, (![B_319, A_320]: (l1_pre_topc(B_319) | ~m1_pre_topc(B_319, A_320) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.13/5.17  tff(c_125, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_116])).
% 12.13/5.17  tff(c_132, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_125])).
% 12.13/5.17  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.13/5.17  tff(c_89, plain, (![A_317]: (u1_struct_0(A_317)=k2_struct_0(A_317) | ~l1_struct_0(A_317))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.13/5.17  tff(c_93, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_12, c_89])).
% 12.13/5.17  tff(c_140, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_132, c_93])).
% 12.13/5.17  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_150, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_50])).
% 12.13/5.17  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_167, plain, (![B_324, A_325]: (v2_pre_topc(B_324) | ~m1_pre_topc(B_324, A_325) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.13/5.17  tff(c_176, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_167])).
% 12.13/5.17  tff(c_183, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_176])).
% 12.13/5.17  tff(c_32, plain, (![A_56]: (m1_pre_topc(A_56, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.13/5.17  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_122, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_116])).
% 12.13/5.17  tff(c_129, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_122])).
% 12.13/5.17  tff(c_136, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_129, c_93])).
% 12.13/5.17  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_141, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_52])).
% 12.13/5.17  tff(c_451, plain, (![A_342, B_343]: (m1_pre_topc(A_342, B_343) | ~m1_pre_topc(A_342, g1_pre_topc(u1_struct_0(B_343), u1_pre_topc(B_343))) | ~l1_pre_topc(B_343) | ~l1_pre_topc(A_342))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.13/5.17  tff(c_464, plain, (![A_342]: (m1_pre_topc(A_342, '#skF_3') | ~m1_pre_topc(A_342, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_342))), inference(superposition, [status(thm), theory('equality')], [c_136, c_451])).
% 12.13/5.17  tff(c_488, plain, (![A_344]: (m1_pre_topc(A_344, '#skF_3') | ~m1_pre_topc(A_344, '#skF_4') | ~l1_pre_topc(A_344))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_141, c_464])).
% 12.13/5.17  tff(c_184, plain, (![B_326, A_327]: (r1_tarski(u1_struct_0(B_326), u1_struct_0(A_327)) | ~m1_pre_topc(B_326, A_327) | ~l1_pre_topc(A_327))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.13/5.17  tff(c_198, plain, (![B_326]: (r1_tarski(u1_struct_0(B_326), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_326, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_184])).
% 12.13/5.17  tff(c_315, plain, (![B_333]: (r1_tarski(u1_struct_0(B_333), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_333, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_198])).
% 12.13/5.17  tff(c_320, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_315])).
% 12.13/5.17  tff(c_429, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_320])).
% 12.13/5.17  tff(c_491, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_488, c_429])).
% 12.13/5.17  tff(c_515, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_491])).
% 12.13/5.17  tff(c_536, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_515])).
% 12.13/5.17  tff(c_540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_536])).
% 12.13/5.17  tff(c_542, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_320])).
% 12.13/5.17  tff(c_367, plain, (![A_338, B_339]: (m1_pre_topc(A_338, g1_pre_topc(u1_struct_0(B_339), u1_pre_topc(B_339))) | ~m1_pre_topc(A_338, B_339) | ~l1_pre_topc(B_339) | ~l1_pre_topc(A_338))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.13/5.17  tff(c_381, plain, (![A_338]: (m1_pre_topc(A_338, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_338, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_338))), inference(superposition, [status(thm), theory('equality')], [c_136, c_367])).
% 12.13/5.17  tff(c_394, plain, (![A_338]: (m1_pre_topc(A_338, '#skF_4') | ~m1_pre_topc(A_338, '#skF_3') | ~l1_pre_topc(A_338))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_141, c_381])).
% 12.13/5.17  tff(c_545, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_542, c_394])).
% 12.13/5.17  tff(c_556, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_545])).
% 12.13/5.17  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_98, plain, (![A_318]: (u1_struct_0(A_318)=k2_struct_0(A_318) | ~l1_pre_topc(A_318))), inference(resolution, [status(thm)], [c_12, c_89])).
% 12.13/5.17  tff(c_106, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_98])).
% 12.13/5.17  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_111, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_56])).
% 12.13/5.17  tff(c_149, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_111])).
% 12.13/5.17  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_147, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_54])).
% 12.13/5.17  tff(c_148, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_147])).
% 12.13/5.17  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_1051, plain, (![C_364, B_363, D_362, E_361, A_365]: (k3_tmap_1(A_365, B_363, C_364, D_362, E_361)=k2_partfun1(u1_struct_0(C_364), u1_struct_0(B_363), E_361, u1_struct_0(D_362)) | ~m1_pre_topc(D_362, C_364) | ~m1_subset_1(E_361, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364), u1_struct_0(B_363)))) | ~v1_funct_2(E_361, u1_struct_0(C_364), u1_struct_0(B_363)) | ~v1_funct_1(E_361) | ~m1_pre_topc(D_362, A_365) | ~m1_pre_topc(C_364, A_365) | ~l1_pre_topc(B_363) | ~v2_pre_topc(B_363) | v2_struct_0(B_363) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.13/5.17  tff(c_1057, plain, (![A_365, B_363, D_362, E_361]: (k3_tmap_1(A_365, B_363, '#skF_4', D_362, E_361)=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_363), E_361, u1_struct_0(D_362)) | ~m1_pre_topc(D_362, '#skF_4') | ~m1_subset_1(E_361, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_363)))) | ~v1_funct_2(E_361, u1_struct_0('#skF_4'), u1_struct_0(B_363)) | ~v1_funct_1(E_361) | ~m1_pre_topc(D_362, A_365) | ~m1_pre_topc('#skF_4', A_365) | ~l1_pre_topc(B_363) | ~v2_pre_topc(B_363) | v2_struct_0(B_363) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365) | v2_struct_0(A_365))), inference(superposition, [status(thm), theory('equality')], [c_140, c_1051])).
% 12.13/5.17  tff(c_13714, plain, (![A_760, B_761, D_762, E_763]: (k3_tmap_1(A_760, B_761, '#skF_4', D_762, E_763)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_761), E_763, u1_struct_0(D_762)) | ~m1_pre_topc(D_762, '#skF_4') | ~m1_subset_1(E_763, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_761)))) | ~v1_funct_2(E_763, k2_struct_0('#skF_4'), u1_struct_0(B_761)) | ~v1_funct_1(E_763) | ~m1_pre_topc(D_762, A_760) | ~m1_pre_topc('#skF_4', A_760) | ~l1_pre_topc(B_761) | ~v2_pre_topc(B_761) | v2_struct_0(B_761) | ~l1_pre_topc(A_760) | ~v2_pre_topc(A_760) | v2_struct_0(A_760))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_140, c_1057])).
% 12.13/5.17  tff(c_13720, plain, (![A_760, D_762, E_763]: (k3_tmap_1(A_760, '#skF_2', '#skF_4', D_762, E_763)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), E_763, u1_struct_0(D_762)) | ~m1_pre_topc(D_762, '#skF_4') | ~m1_subset_1(E_763, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_763, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_763) | ~m1_pre_topc(D_762, A_760) | ~m1_pre_topc('#skF_4', A_760) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_760) | ~v2_pre_topc(A_760) | v2_struct_0(A_760))), inference(superposition, [status(thm), theory('equality')], [c_106, c_13714])).
% 12.13/5.17  tff(c_13730, plain, (![A_760, D_762, E_763]: (k3_tmap_1(A_760, '#skF_2', '#skF_4', D_762, E_763)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_763, u1_struct_0(D_762)) | ~m1_pre_topc(D_762, '#skF_4') | ~m1_subset_1(E_763, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_763, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_763) | ~m1_pre_topc(D_762, A_760) | ~m1_pre_topc('#skF_4', A_760) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_760) | ~v2_pre_topc(A_760) | v2_struct_0(A_760))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_106, c_106, c_13720])).
% 12.13/5.17  tff(c_13903, plain, (![A_766, D_767, E_768]: (k3_tmap_1(A_766, '#skF_2', '#skF_4', D_767, E_768)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_768, u1_struct_0(D_767)) | ~m1_pre_topc(D_767, '#skF_4') | ~m1_subset_1(E_768, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_768, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_768) | ~m1_pre_topc(D_767, A_766) | ~m1_pre_topc('#skF_4', A_766) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766) | v2_struct_0(A_766))), inference(negUnitSimplification, [status(thm)], [c_72, c_13730])).
% 12.13/5.17  tff(c_13905, plain, (![A_766, D_767]: (k3_tmap_1(A_766, '#skF_2', '#skF_4', D_767, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_767)) | ~m1_pre_topc(D_767, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_767, A_766) | ~m1_pre_topc('#skF_4', A_766) | ~l1_pre_topc(A_766) | ~v2_pre_topc(A_766) | v2_struct_0(A_766))), inference(resolution, [status(thm)], [c_148, c_13903])).
% 12.13/5.17  tff(c_19176, plain, (![A_883, D_884]: (k3_tmap_1(A_883, '#skF_2', '#skF_4', D_884, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_884)) | ~m1_pre_topc(D_884, '#skF_4') | ~m1_pre_topc(D_884, A_883) | ~m1_pre_topc('#skF_4', A_883) | ~l1_pre_topc(A_883) | ~v2_pre_topc(A_883) | v2_struct_0(A_883))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_149, c_13905])).
% 12.13/5.17  tff(c_19254, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_556, c_19176])).
% 12.13/5.17  tff(c_19362, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_132, c_556, c_140, c_19254])).
% 12.13/5.17  tff(c_19363, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_19362])).
% 12.13/5.17  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_399, plain, (![A_340]: (m1_pre_topc(A_340, '#skF_4') | ~m1_pre_topc(A_340, '#skF_3') | ~l1_pre_topc(A_340))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_141, c_381])).
% 12.13/5.17  tff(c_407, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_399])).
% 12.13/5.17  tff(c_413, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_129, c_407])).
% 12.13/5.17  tff(c_541, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_320])).
% 12.13/5.17  tff(c_192, plain, (![B_326]: (r1_tarski(u1_struct_0(B_326), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_326, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_184])).
% 12.13/5.17  tff(c_220, plain, (![B_328]: (r1_tarski(u1_struct_0(B_328), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_328, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_192])).
% 12.13/5.17  tff(c_228, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_136, c_220])).
% 12.13/5.17  tff(c_702, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_228])).
% 12.13/5.17  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.13/5.17  tff(c_704, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_702, c_2])).
% 12.13/5.17  tff(c_707, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_704])).
% 12.13/5.17  tff(c_738, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_707, c_136])).
% 12.13/5.17  tff(c_19266, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_19176])).
% 12.13/5.17  tff(c_19379, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_60, c_413, c_738, c_19266])).
% 12.13/5.17  tff(c_19380, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_19379])).
% 12.13/5.17  tff(c_19409, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_19363, c_19380])).
% 12.13/5.17  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 12.13/5.17  tff(c_19410, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19409, c_80])).
% 12.13/5.17  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_251])).
% 12.13/5.17  tff(c_20, plain, (![A_14]: (v3_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.13/5.17  tff(c_30, plain, (![B_55, A_53]: (m1_subset_1(u1_struct_0(B_55), k1_zfmisc_1(u1_struct_0(A_53))) | ~m1_pre_topc(B_55, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.13/5.17  tff(c_952, plain, (![B_359, A_360]: (v1_tsep_1(B_359, A_360) | ~v3_pre_topc(u1_struct_0(B_359), A_360) | ~m1_subset_1(u1_struct_0(B_359), k1_zfmisc_1(u1_struct_0(A_360))) | ~m1_pre_topc(B_359, A_360) | ~l1_pre_topc(A_360) | ~v2_pre_topc(A_360))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.13/5.17  tff(c_1906, plain, (![B_427, A_428]: (v1_tsep_1(B_427, A_428) | ~v3_pre_topc(u1_struct_0(B_427), A_428) | ~v2_pre_topc(A_428) | ~m1_pre_topc(B_427, A_428) | ~l1_pre_topc(A_428))), inference(resolution, [status(thm)], [c_30, c_952])).
% 12.13/5.17  tff(c_2317, plain, (![A_457]: (v1_tsep_1('#skF_3', A_457) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_457) | ~v2_pre_topc(A_457) | ~m1_pre_topc('#skF_3', A_457) | ~l1_pre_topc(A_457))), inference(superposition, [status(thm), theory('equality')], [c_738, c_1906])).
% 12.13/5.17  tff(c_2327, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_2317])).
% 12.13/5.17  tff(c_2334, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_132, c_413, c_2327])).
% 12.13/5.17  tff(c_19258, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_413, c_19176])).
% 12.13/5.17  tff(c_19370, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_132, c_556, c_413, c_738, c_19258])).
% 12.13/5.17  tff(c_19371, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_19370])).
% 12.13/5.17  tff(c_19399, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_19363, c_19371])).
% 12.13/5.17  tff(c_38, plain, (![D_179, C_163, B_131, A_67, G_193, E_187]: (r1_tmap_1(D_179, A_67, E_187, G_193) | ~r1_tmap_1(C_163, A_67, k3_tmap_1(B_131, A_67, D_179, C_163, E_187), G_193) | ~m1_subset_1(G_193, u1_struct_0(C_163)) | ~m1_subset_1(G_193, u1_struct_0(D_179)) | ~m1_pre_topc(C_163, D_179) | ~v1_tsep_1(C_163, B_131) | ~m1_subset_1(E_187, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_179), u1_struct_0(A_67)))) | ~v1_funct_2(E_187, u1_struct_0(D_179), u1_struct_0(A_67)) | ~v1_funct_1(E_187) | ~m1_pre_topc(D_179, B_131) | v2_struct_0(D_179) | ~m1_pre_topc(C_163, B_131) | v2_struct_0(C_163) | ~l1_pre_topc(B_131) | ~v2_pre_topc(B_131) | v2_struct_0(B_131) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_202])).
% 12.13/5.17  tff(c_19402, plain, (![G_193]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_193) | ~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5'), G_193) | ~m1_subset_1(G_193, u1_struct_0('#skF_3')) | ~m1_subset_1(G_193, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_19399, c_38])).
% 12.13/5.17  tff(c_19406, plain, (![G_193]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_193) | ~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5'), G_193) | ~m1_subset_1(G_193, k2_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_183, c_132, c_413, c_556, c_58, c_149, c_106, c_140, c_148, c_106, c_140, c_2334, c_413, c_140, c_738, c_19402])).
% 12.13/5.17  tff(c_19629, plain, (![G_890]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_890) | ~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_4', '#skF_5'), G_890) | ~m1_subset_1(G_890, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_66, c_19406])).
% 12.13/5.17  tff(c_19632, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_19410, c_19629])).
% 12.13/5.17  tff(c_19635, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_19632])).
% 12.13/5.17  tff(c_19637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_19635])).
% 12.13/5.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.13/5.17  
% 12.13/5.17  Inference rules
% 12.13/5.17  ----------------------
% 12.13/5.17  #Ref     : 0
% 12.13/5.17  #Sup     : 4223
% 12.13/5.17  #Fact    : 0
% 12.13/5.18  #Define  : 0
% 12.13/5.18  #Split   : 17
% 12.13/5.18  #Chain   : 0
% 12.13/5.18  #Close   : 0
% 12.13/5.18  
% 12.13/5.18  Ordering : KBO
% 12.13/5.18  
% 12.13/5.18  Simplification rules
% 12.13/5.18  ----------------------
% 12.13/5.18  #Subsume      : 2457
% 12.13/5.18  #Demod        : 9780
% 12.13/5.18  #Tautology    : 683
% 12.13/5.18  #SimpNegUnit  : 168
% 12.13/5.18  #BackRed      : 14
% 12.13/5.18  
% 12.13/5.18  #Partial instantiations: 0
% 12.13/5.18  #Strategies tried      : 1
% 12.13/5.18  
% 12.13/5.18  Timing (in seconds)
% 12.13/5.18  ----------------------
% 12.13/5.18  Preprocessing        : 0.40
% 12.13/5.18  Parsing              : 0.20
% 12.13/5.18  CNF conversion       : 0.05
% 12.13/5.18  Main loop            : 3.99
% 12.13/5.18  Inferencing          : 0.76
% 12.13/5.18  Reduction            : 1.53
% 12.13/5.18  Demodulation         : 1.19
% 12.13/5.18  BG Simplification    : 0.07
% 12.13/5.18  Subsumption          : 1.47
% 12.13/5.18  Abstraction          : 0.16
% 12.13/5.18  MUC search           : 0.00
% 12.13/5.18  Cooper               : 0.00
% 12.13/5.18  Total                : 4.43
% 12.13/5.18  Index Insertion      : 0.00
% 12.13/5.18  Index Deletion       : 0.00
% 12.13/5.18  Index Matching       : 0.00
% 12.13/5.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
