%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:36 EST 2020

% Result     : Theorem 20.77s
% Output     : CNFRefutation 20.86s
% Verified   : 
% Statistics : Number of formulae       :  162 (2200 expanded)
%              Number of leaves         :   47 ( 768 expanded)
%              Depth                    :   23
%              Number of atoms          :  467 (10121 expanded)
%              Number of equality atoms :   47 (1222 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_299,negated_conjecture,(
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

tff(f_196,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_189,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

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

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_136,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_185,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_154,axiom,(
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

tff(f_238,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(c_50,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_82,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_124,plain,(
    ! [B_280,A_281] :
      ( l1_pre_topc(B_280)
      | ~ m1_pre_topc(B_280,A_281)
      | ~ l1_pre_topc(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_130,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_124])).

tff(c_137,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_130])).

tff(c_12,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,(
    ! [A_278] :
      ( u1_struct_0(A_278) = k2_struct_0(A_278)
      | ~ l1_struct_0(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_105,plain,(
    ! [A_7] :
      ( u1_struct_0(A_7) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_144,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_137,c_105])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_150,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_58])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_84,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_72,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_133,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_124])).

tff(c_140,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_133])).

tff(c_148,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_105])).

tff(c_191,plain,(
    ! [B_287,A_288] :
      ( r1_tarski(u1_struct_0(B_287),u1_struct_0(A_288))
      | ~ m1_pre_topc(B_287,A_288)
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_205,plain,(
    ! [B_287] :
      ( r1_tarski(u1_struct_0(B_287),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_287,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_191])).

tff(c_244,plain,(
    ! [B_290] :
      ( r1_tarski(u1_struct_0(B_290),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_290,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_205])).

tff(c_249,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_244])).

tff(c_491,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_40,plain,(
    ! [A_81] :
      ( m1_pre_topc(A_81,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_60,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_156,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_60])).

tff(c_492,plain,(
    ! [A_304,B_305] :
      ( m1_pre_topc(A_304,g1_pre_topc(u1_struct_0(B_305),u1_pre_topc(B_305)))
      | ~ m1_pre_topc(A_304,B_305)
      | ~ l1_pre_topc(B_305)
      | ~ l1_pre_topc(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_506,plain,(
    ! [A_304] :
      ( m1_pre_topc(A_304,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_304,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_492])).

tff(c_534,plain,(
    ! [A_306] :
      ( m1_pre_topc(A_306,'#skF_4')
      | ~ m1_pre_topc(A_306,'#skF_3')
      | ~ l1_pre_topc(A_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_156,c_506])).

tff(c_548,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_534])).

tff(c_559,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_548])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_559])).

tff(c_563,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_341,plain,(
    ! [B_295,A_296] :
      ( m1_pre_topc(B_295,A_296)
      | ~ m1_pre_topc(B_295,g1_pre_topc(u1_struct_0(A_296),u1_pre_topc(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_344,plain,(
    ! [B_295] :
      ( m1_pre_topc(B_295,'#skF_3')
      | ~ m1_pre_topc(B_295,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_341])).

tff(c_359,plain,(
    ! [B_295] :
      ( m1_pre_topc(B_295,'#skF_3')
      | ~ m1_pre_topc(B_295,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_156,c_344])).

tff(c_199,plain,(
    ! [B_287] :
      ( r1_tarski(u1_struct_0(B_287),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_287,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_191])).

tff(c_227,plain,(
    ! [B_289] :
      ( r1_tarski(u1_struct_0(B_289),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_289,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_199])).

tff(c_235,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_227])).

tff(c_401,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_405,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_359,c_401])).

tff(c_408,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_405])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_408])).

tff(c_414,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_413,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_562,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_605,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_562,c_2])).

tff(c_608,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_605])).

tff(c_613,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_156])).

tff(c_615,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_148])).

tff(c_671,plain,(
    ! [A_308,B_309] :
      ( m1_pre_topc(A_308,g1_pre_topc(u1_struct_0(B_309),u1_pre_topc(B_309)))
      | ~ m1_pre_topc(A_308,B_309)
      | ~ l1_pre_topc(B_309)
      | ~ l1_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_689,plain,(
    ! [A_308] :
      ( m1_pre_topc(A_308,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_308,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_308) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_671])).

tff(c_758,plain,(
    ! [A_312] :
      ( m1_pre_topc(A_312,'#skF_4')
      | ~ m1_pre_topc(A_312,'#skF_3')
      | ~ l1_pre_topc(A_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_613,c_689])).

tff(c_765,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_414,c_758])).

tff(c_778,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_765])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_76,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_106,plain,(
    ! [A_279] :
      ( u1_struct_0(A_279) = k2_struct_0(A_279)
      | ~ l1_pre_topc(A_279) ) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_114,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_106])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_119,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_64])).

tff(c_149,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_119])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_155,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_114,c_62])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_78,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_174,plain,(
    ! [B_285,A_286] :
      ( v2_pre_topc(B_285)
      | ~ m1_pre_topc(B_285,A_286)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_180,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_174])).

tff(c_187,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_180])).

tff(c_1406,plain,(
    ! [A_343,B_344,C_345,D_346] :
      ( k2_partfun1(u1_struct_0(A_343),u1_struct_0(B_344),C_345,u1_struct_0(D_346)) = k2_tmap_1(A_343,B_344,C_345,D_346)
      | ~ m1_pre_topc(D_346,A_343)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_343),u1_struct_0(B_344))))
      | ~ v1_funct_2(C_345,u1_struct_0(A_343),u1_struct_0(B_344))
      | ~ v1_funct_1(C_345)
      | ~ l1_pre_topc(B_344)
      | ~ v2_pre_topc(B_344)
      | v2_struct_0(B_344)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1412,plain,(
    ! [B_344,C_345,D_346] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_344),C_345,u1_struct_0(D_346)) = k2_tmap_1('#skF_4',B_344,C_345,D_346)
      | ~ m1_pre_topc(D_346,'#skF_4')
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_344))))
      | ~ v1_funct_2(C_345,u1_struct_0('#skF_4'),u1_struct_0(B_344))
      | ~ v1_funct_1(C_345)
      | ~ l1_pre_topc(B_344)
      | ~ v2_pre_topc(B_344)
      | v2_struct_0(B_344)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1406])).

tff(c_1430,plain,(
    ! [B_344,C_345,D_346] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_344),C_345,u1_struct_0(D_346)) = k2_tmap_1('#skF_4',B_344,C_345,D_346)
      | ~ m1_pre_topc(D_346,'#skF_4')
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_344))))
      | ~ v1_funct_2(C_345,k2_struct_0('#skF_4'),u1_struct_0(B_344))
      | ~ v1_funct_1(C_345)
      | ~ l1_pre_topc(B_344)
      | ~ v2_pre_topc(B_344)
      | v2_struct_0(B_344)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_137,c_144,c_144,c_1412])).

tff(c_6747,plain,(
    ! [B_538,C_539,D_540] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_538),C_539,u1_struct_0(D_540)) = k2_tmap_1('#skF_4',B_538,C_539,D_540)
      | ~ m1_pre_topc(D_540,'#skF_4')
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_538))))
      | ~ v1_funct_2(C_539,k2_struct_0('#skF_4'),u1_struct_0(B_538))
      | ~ v1_funct_1(C_539)
      | ~ l1_pre_topc(B_538)
      | ~ v2_pre_topc(B_538)
      | v2_struct_0(B_538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1430])).

tff(c_6753,plain,(
    ! [C_539,D_540] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_539,u1_struct_0(D_540)) = k2_tmap_1('#skF_4','#skF_2',C_539,D_540)
      | ~ m1_pre_topc(D_540,'#skF_4')
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_539,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_539)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_6747])).

tff(c_6763,plain,(
    ! [C_539,D_540] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_539,u1_struct_0(D_540)) = k2_tmap_1('#skF_4','#skF_2',C_539,D_540)
      | ~ m1_pre_topc(D_540,'#skF_4')
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_539,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_539)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_114,c_114,c_6753])).

tff(c_7068,plain,(
    ! [C_552,D_553] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_552,u1_struct_0(D_553)) = k2_tmap_1('#skF_4','#skF_2',C_552,D_553)
      | ~ m1_pre_topc(D_553,'#skF_4')
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_552,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_552) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6763])).

tff(c_7070,plain,(
    ! [D_553] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_553)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_553)
      | ~ m1_pre_topc(D_553,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_155,c_7068])).

tff(c_7074,plain,(
    ! [D_554] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_554)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_554)
      | ~ m1_pre_topc(D_554,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_149,c_7070])).

tff(c_7086,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_7074])).

tff(c_7098,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_7086])).

tff(c_1695,plain,(
    ! [E_360,A_357,C_361,B_359,D_358] :
      ( k3_tmap_1(A_357,B_359,C_361,D_358,E_360) = k2_partfun1(u1_struct_0(C_361),u1_struct_0(B_359),E_360,u1_struct_0(D_358))
      | ~ m1_pre_topc(D_358,C_361)
      | ~ m1_subset_1(E_360,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_361),u1_struct_0(B_359))))
      | ~ v1_funct_2(E_360,u1_struct_0(C_361),u1_struct_0(B_359))
      | ~ v1_funct_1(E_360)
      | ~ m1_pre_topc(D_358,A_357)
      | ~ m1_pre_topc(C_361,A_357)
      | ~ l1_pre_topc(B_359)
      | ~ v2_pre_topc(B_359)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | v2_struct_0(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1701,plain,(
    ! [A_357,B_359,D_358,E_360] :
      ( k3_tmap_1(A_357,B_359,'#skF_4',D_358,E_360) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_359),E_360,u1_struct_0(D_358))
      | ~ m1_pre_topc(D_358,'#skF_4')
      | ~ m1_subset_1(E_360,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_359))))
      | ~ v1_funct_2(E_360,u1_struct_0('#skF_4'),u1_struct_0(B_359))
      | ~ v1_funct_1(E_360)
      | ~ m1_pre_topc(D_358,A_357)
      | ~ m1_pre_topc('#skF_4',A_357)
      | ~ l1_pre_topc(B_359)
      | ~ v2_pre_topc(B_359)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | v2_struct_0(A_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_1695])).

tff(c_25155,plain,(
    ! [A_861,B_862,D_863,E_864] :
      ( k3_tmap_1(A_861,B_862,'#skF_4',D_863,E_864) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_862),E_864,u1_struct_0(D_863))
      | ~ m1_pre_topc(D_863,'#skF_4')
      | ~ m1_subset_1(E_864,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_862))))
      | ~ v1_funct_2(E_864,k2_struct_0('#skF_4'),u1_struct_0(B_862))
      | ~ v1_funct_1(E_864)
      | ~ m1_pre_topc(D_863,A_861)
      | ~ m1_pre_topc('#skF_4',A_861)
      | ~ l1_pre_topc(B_862)
      | ~ v2_pre_topc(B_862)
      | v2_struct_0(B_862)
      | ~ l1_pre_topc(A_861)
      | ~ v2_pre_topc(A_861)
      | v2_struct_0(A_861) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_144,c_1701])).

tff(c_25161,plain,(
    ! [A_861,D_863,E_864] :
      ( k3_tmap_1(A_861,'#skF_2','#skF_4',D_863,E_864) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),E_864,u1_struct_0(D_863))
      | ~ m1_pre_topc(D_863,'#skF_4')
      | ~ m1_subset_1(E_864,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_864,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_864)
      | ~ m1_pre_topc(D_863,A_861)
      | ~ m1_pre_topc('#skF_4',A_861)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_861)
      | ~ v2_pre_topc(A_861)
      | v2_struct_0(A_861) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_25155])).

tff(c_25171,plain,(
    ! [A_861,D_863,E_864] :
      ( k3_tmap_1(A_861,'#skF_2','#skF_4',D_863,E_864) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_864,u1_struct_0(D_863))
      | ~ m1_pre_topc(D_863,'#skF_4')
      | ~ m1_subset_1(E_864,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_864,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_864)
      | ~ m1_pre_topc(D_863,A_861)
      | ~ m1_pre_topc('#skF_4',A_861)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_861)
      | ~ v2_pre_topc(A_861)
      | v2_struct_0(A_861) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_114,c_114,c_25161])).

tff(c_42403,plain,(
    ! [A_1144,D_1145,E_1146] :
      ( k3_tmap_1(A_1144,'#skF_2','#skF_4',D_1145,E_1146) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_1146,u1_struct_0(D_1145))
      | ~ m1_pre_topc(D_1145,'#skF_4')
      | ~ m1_subset_1(E_1146,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_1146,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_1146)
      | ~ m1_pre_topc(D_1145,A_1144)
      | ~ m1_pre_topc('#skF_4',A_1144)
      | ~ l1_pre_topc(A_1144)
      | ~ v2_pre_topc(A_1144)
      | v2_struct_0(A_1144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_25171])).

tff(c_42405,plain,(
    ! [A_1144,D_1145] :
      ( k3_tmap_1(A_1144,'#skF_2','#skF_4',D_1145,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_1145))
      | ~ m1_pre_topc(D_1145,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_1145,A_1144)
      | ~ m1_pre_topc('#skF_4',A_1144)
      | ~ l1_pre_topc(A_1144)
      | ~ v2_pre_topc(A_1144)
      | v2_struct_0(A_1144) ) ),
    inference(resolution,[status(thm)],[c_155,c_42403])).

tff(c_42409,plain,(
    ! [A_1147,D_1148] :
      ( k3_tmap_1(A_1147,'#skF_2','#skF_4',D_1148,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_1148))
      | ~ m1_pre_topc(D_1148,'#skF_4')
      | ~ m1_pre_topc(D_1148,A_1147)
      | ~ m1_pre_topc('#skF_4',A_1147)
      | ~ l1_pre_topc(A_1147)
      | ~ v2_pre_topc(A_1147)
      | v2_struct_0(A_1147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_149,c_42405])).

tff(c_42525,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_42409])).

tff(c_42660,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_68,c_563,c_7098,c_615,c_42525])).

tff(c_42661,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_42660])).

tff(c_54,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_52,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_88,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_42674,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42661,c_88])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_22,plain,(
    ! [A_17] :
      ( v3_pre_topc(k2_struct_0(A_17),A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [B_80,A_78] :
      ( m1_subset_1(u1_struct_0(B_80),k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_pre_topc(B_80,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_944,plain,(
    ! [B_319,A_320] :
      ( v1_tsep_1(B_319,A_320)
      | ~ v3_pre_topc(u1_struct_0(B_319),A_320)
      | ~ m1_subset_1(u1_struct_0(B_319),k1_zfmisc_1(u1_struct_0(A_320)))
      | ~ m1_pre_topc(B_319,A_320)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2114,plain,(
    ! [B_387,A_388] :
      ( v1_tsep_1(B_387,A_388)
      | ~ v3_pre_topc(u1_struct_0(B_387),A_388)
      | ~ v2_pre_topc(A_388)
      | ~ m1_pre_topc(B_387,A_388)
      | ~ l1_pre_topc(A_388) ) ),
    inference(resolution,[status(thm)],[c_38,c_944])).

tff(c_2677,plain,(
    ! [A_417] :
      ( v1_tsep_1('#skF_3',A_417)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_417)
      | ~ v2_pre_topc(A_417)
      | ~ m1_pre_topc('#skF_3',A_417)
      | ~ l1_pre_topc(A_417) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_2114])).

tff(c_2687,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_2677])).

tff(c_2694,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_137,c_563,c_2687])).

tff(c_7083,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_7074])).

tff(c_7096,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_7083])).

tff(c_7103,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7098,c_7096])).

tff(c_44,plain,(
    ! [A_85,D_141,C_133,F_147,B_117] :
      ( r1_tmap_1(B_117,A_85,C_133,F_147)
      | ~ r1_tmap_1(D_141,A_85,k2_tmap_1(B_117,A_85,C_133,D_141),F_147)
      | ~ m1_subset_1(F_147,u1_struct_0(D_141))
      | ~ m1_subset_1(F_147,u1_struct_0(B_117))
      | ~ m1_pre_topc(D_141,B_117)
      | ~ v1_tsep_1(D_141,B_117)
      | v2_struct_0(D_141)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_117),u1_struct_0(A_85))))
      | ~ v1_funct_2(C_133,u1_struct_0(B_117),u1_struct_0(A_85))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_117)
      | ~ v2_pre_topc(B_117)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_7110,plain,(
    ! [F_147] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_147)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_147)
      | ~ m1_subset_1(F_147,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_147,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ v1_tsep_1('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7103,c_44])).

tff(c_7114,plain,(
    ! [F_147] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_147)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_147)
      | ~ m1_subset_1(F_147,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_187,c_137,c_66,c_149,c_114,c_144,c_155,c_114,c_144,c_2694,c_563,c_144,c_615,c_7110])).

tff(c_7115,plain,(
    ! [F_147] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_147)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_147)
      | ~ m1_subset_1(F_147,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_70,c_74,c_7114])).

tff(c_42919,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42674,c_7115])).

tff(c_42925,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_42919])).

tff(c_42927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42925])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:43:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.77/11.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.86/11.92  
% 20.86/11.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.86/11.92  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 20.86/11.92  
% 20.86/11.92  %Foreground sorts:
% 20.86/11.92  
% 20.86/11.92  
% 20.86/11.92  %Background operators:
% 20.86/11.92  
% 20.86/11.92  
% 20.86/11.92  %Foreground operators:
% 20.86/11.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 20.86/11.92  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 20.86/11.92  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 20.86/11.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.86/11.92  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 20.86/11.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.86/11.92  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 20.86/11.92  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 20.86/11.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.86/11.92  tff('#skF_7', type, '#skF_7': $i).
% 20.86/11.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.86/11.92  tff('#skF_5', type, '#skF_5': $i).
% 20.86/11.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 20.86/11.92  tff('#skF_6', type, '#skF_6': $i).
% 20.86/11.92  tff('#skF_2', type, '#skF_2': $i).
% 20.86/11.92  tff('#skF_3', type, '#skF_3': $i).
% 20.86/11.92  tff('#skF_1', type, '#skF_1': $i).
% 20.86/11.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.86/11.92  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 20.86/11.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.86/11.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.86/11.92  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 20.86/11.92  tff('#skF_4', type, '#skF_4': $i).
% 20.86/11.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.86/11.92  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 20.86/11.92  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 20.86/11.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.86/11.92  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 20.86/11.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.86/11.92  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 20.86/11.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.86/11.92  
% 20.86/11.95  tff(f_299, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 20.86/11.95  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 20.86/11.95  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 20.86/11.95  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 20.86/11.95  tff(f_196, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 20.86/11.95  tff(f_189, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 20.86/11.95  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 20.86/11.95  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 20.86/11.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.86/11.95  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 20.86/11.95  tff(f_104, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 20.86/11.95  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 20.86/11.95  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 20.86/11.95  tff(f_185, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 20.86/11.95  tff(f_154, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 20.86/11.95  tff(f_238, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 20.86/11.95  tff(c_50, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_82, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_124, plain, (![B_280, A_281]: (l1_pre_topc(B_280) | ~m1_pre_topc(B_280, A_281) | ~l1_pre_topc(A_281))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.86/11.95  tff(c_130, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_124])).
% 20.86/11.95  tff(c_137, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_130])).
% 20.86/11.95  tff(c_12, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 20.86/11.95  tff(c_101, plain, (![A_278]: (u1_struct_0(A_278)=k2_struct_0(A_278) | ~l1_struct_0(A_278))), inference(cnfTransformation, [status(thm)], [f_44])).
% 20.86/11.95  tff(c_105, plain, (![A_7]: (u1_struct_0(A_7)=k2_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(resolution, [status(thm)], [c_12, c_101])).
% 20.86/11.95  tff(c_144, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_137, c_105])).
% 20.86/11.95  tff(c_58, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_150, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_58])).
% 20.86/11.95  tff(c_86, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_84, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_72, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_133, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_72, c_124])).
% 20.86/11.95  tff(c_140, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_133])).
% 20.86/11.95  tff(c_148, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_140, c_105])).
% 20.86/11.95  tff(c_191, plain, (![B_287, A_288]: (r1_tarski(u1_struct_0(B_287), u1_struct_0(A_288)) | ~m1_pre_topc(B_287, A_288) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_196])).
% 20.86/11.95  tff(c_205, plain, (![B_287]: (r1_tarski(u1_struct_0(B_287), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_287, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_191])).
% 20.86/11.95  tff(c_244, plain, (![B_290]: (r1_tarski(u1_struct_0(B_290), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_290, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_205])).
% 20.86/11.95  tff(c_249, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_148, c_244])).
% 20.86/11.95  tff(c_491, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_249])).
% 20.86/11.95  tff(c_40, plain, (![A_81]: (m1_pre_topc(A_81, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_189])).
% 20.86/11.95  tff(c_60, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_156, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_60])).
% 20.86/11.95  tff(c_492, plain, (![A_304, B_305]: (m1_pre_topc(A_304, g1_pre_topc(u1_struct_0(B_305), u1_pre_topc(B_305))) | ~m1_pre_topc(A_304, B_305) | ~l1_pre_topc(B_305) | ~l1_pre_topc(A_304))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.86/11.95  tff(c_506, plain, (![A_304]: (m1_pre_topc(A_304, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_304, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_304))), inference(superposition, [status(thm), theory('equality')], [c_148, c_492])).
% 20.86/11.95  tff(c_534, plain, (![A_306]: (m1_pre_topc(A_306, '#skF_4') | ~m1_pre_topc(A_306, '#skF_3') | ~l1_pre_topc(A_306))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_156, c_506])).
% 20.86/11.95  tff(c_548, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_534])).
% 20.86/11.95  tff(c_559, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_548])).
% 20.86/11.95  tff(c_561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_491, c_559])).
% 20.86/11.95  tff(c_563, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_249])).
% 20.86/11.95  tff(c_341, plain, (![B_295, A_296]: (m1_pre_topc(B_295, A_296) | ~m1_pre_topc(B_295, g1_pre_topc(u1_struct_0(A_296), u1_pre_topc(A_296))) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_62])).
% 20.86/11.95  tff(c_344, plain, (![B_295]: (m1_pre_topc(B_295, '#skF_3') | ~m1_pre_topc(B_295, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_341])).
% 20.86/11.95  tff(c_359, plain, (![B_295]: (m1_pre_topc(B_295, '#skF_3') | ~m1_pre_topc(B_295, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_156, c_344])).
% 20.86/11.95  tff(c_199, plain, (![B_287]: (r1_tarski(u1_struct_0(B_287), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_287, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_191])).
% 20.86/11.95  tff(c_227, plain, (![B_289]: (r1_tarski(u1_struct_0(B_289), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_289, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_199])).
% 20.86/11.95  tff(c_235, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_227])).
% 20.86/11.95  tff(c_401, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_235])).
% 20.86/11.95  tff(c_405, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_359, c_401])).
% 20.86/11.95  tff(c_408, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_405])).
% 20.86/11.95  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_408])).
% 20.86/11.95  tff(c_414, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_235])).
% 20.86/11.95  tff(c_413, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_235])).
% 20.86/11.95  tff(c_562, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_249])).
% 20.86/11.95  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 20.86/11.95  tff(c_605, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_562, c_2])).
% 20.86/11.95  tff(c_608, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_605])).
% 20.86/11.95  tff(c_613, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_156])).
% 20.86/11.95  tff(c_615, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_608, c_148])).
% 20.86/11.95  tff(c_671, plain, (![A_308, B_309]: (m1_pre_topc(A_308, g1_pre_topc(u1_struct_0(B_309), u1_pre_topc(B_309))) | ~m1_pre_topc(A_308, B_309) | ~l1_pre_topc(B_309) | ~l1_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.86/11.95  tff(c_689, plain, (![A_308]: (m1_pre_topc(A_308, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_308, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_308))), inference(superposition, [status(thm), theory('equality')], [c_615, c_671])).
% 20.86/11.95  tff(c_758, plain, (![A_312]: (m1_pre_topc(A_312, '#skF_4') | ~m1_pre_topc(A_312, '#skF_3') | ~l1_pre_topc(A_312))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_613, c_689])).
% 20.86/11.95  tff(c_765, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_414, c_758])).
% 20.86/11.95  tff(c_778, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_765])).
% 20.86/11.95  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_76, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_106, plain, (![A_279]: (u1_struct_0(A_279)=k2_struct_0(A_279) | ~l1_pre_topc(A_279))), inference(resolution, [status(thm)], [c_12, c_101])).
% 20.86/11.95  tff(c_114, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_106])).
% 20.86/11.95  tff(c_64, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_119, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_64])).
% 20.86/11.95  tff(c_149, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_119])).
% 20.86/11.95  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_155, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_114, c_62])).
% 20.86/11.95  tff(c_80, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_78, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_174, plain, (![B_285, A_286]: (v2_pre_topc(B_285) | ~m1_pre_topc(B_285, A_286) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_40])).
% 20.86/11.95  tff(c_180, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_174])).
% 20.86/11.95  tff(c_187, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_180])).
% 20.86/11.95  tff(c_1406, plain, (![A_343, B_344, C_345, D_346]: (k2_partfun1(u1_struct_0(A_343), u1_struct_0(B_344), C_345, u1_struct_0(D_346))=k2_tmap_1(A_343, B_344, C_345, D_346) | ~m1_pre_topc(D_346, A_343) | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_343), u1_struct_0(B_344)))) | ~v1_funct_2(C_345, u1_struct_0(A_343), u1_struct_0(B_344)) | ~v1_funct_1(C_345) | ~l1_pre_topc(B_344) | ~v2_pre_topc(B_344) | v2_struct_0(B_344) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_104])).
% 20.86/11.95  tff(c_1412, plain, (![B_344, C_345, D_346]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_344), C_345, u1_struct_0(D_346))=k2_tmap_1('#skF_4', B_344, C_345, D_346) | ~m1_pre_topc(D_346, '#skF_4') | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_344)))) | ~v1_funct_2(C_345, u1_struct_0('#skF_4'), u1_struct_0(B_344)) | ~v1_funct_1(C_345) | ~l1_pre_topc(B_344) | ~v2_pre_topc(B_344) | v2_struct_0(B_344) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_1406])).
% 20.86/11.95  tff(c_1430, plain, (![B_344, C_345, D_346]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_344), C_345, u1_struct_0(D_346))=k2_tmap_1('#skF_4', B_344, C_345, D_346) | ~m1_pre_topc(D_346, '#skF_4') | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_344)))) | ~v1_funct_2(C_345, k2_struct_0('#skF_4'), u1_struct_0(B_344)) | ~v1_funct_1(C_345) | ~l1_pre_topc(B_344) | ~v2_pre_topc(B_344) | v2_struct_0(B_344) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_137, c_144, c_144, c_1412])).
% 20.86/11.95  tff(c_6747, plain, (![B_538, C_539, D_540]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_538), C_539, u1_struct_0(D_540))=k2_tmap_1('#skF_4', B_538, C_539, D_540) | ~m1_pre_topc(D_540, '#skF_4') | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_538)))) | ~v1_funct_2(C_539, k2_struct_0('#skF_4'), u1_struct_0(B_538)) | ~v1_funct_1(C_539) | ~l1_pre_topc(B_538) | ~v2_pre_topc(B_538) | v2_struct_0(B_538))), inference(negUnitSimplification, [status(thm)], [c_70, c_1430])).
% 20.86/11.95  tff(c_6753, plain, (![C_539, D_540]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_539, u1_struct_0(D_540))=k2_tmap_1('#skF_4', '#skF_2', C_539, D_540) | ~m1_pre_topc(D_540, '#skF_4') | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_539, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_539) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_6747])).
% 20.86/11.95  tff(c_6763, plain, (![C_539, D_540]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_539, u1_struct_0(D_540))=k2_tmap_1('#skF_4', '#skF_2', C_539, D_540) | ~m1_pre_topc(D_540, '#skF_4') | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_539, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_539) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_114, c_114, c_6753])).
% 20.86/11.95  tff(c_7068, plain, (![C_552, D_553]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_552, u1_struct_0(D_553))=k2_tmap_1('#skF_4', '#skF_2', C_552, D_553) | ~m1_pre_topc(D_553, '#skF_4') | ~m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_552, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_552))), inference(negUnitSimplification, [status(thm)], [c_80, c_6763])).
% 20.86/11.95  tff(c_7070, plain, (![D_553]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_553))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_553) | ~m1_pre_topc(D_553, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_155, c_7068])).
% 20.86/11.95  tff(c_7074, plain, (![D_554]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_554))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_554) | ~m1_pre_topc(D_554, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_149, c_7070])).
% 20.86/11.95  tff(c_7086, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_144, c_7074])).
% 20.86/11.95  tff(c_7098, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_778, c_7086])).
% 20.86/11.95  tff(c_1695, plain, (![E_360, A_357, C_361, B_359, D_358]: (k3_tmap_1(A_357, B_359, C_361, D_358, E_360)=k2_partfun1(u1_struct_0(C_361), u1_struct_0(B_359), E_360, u1_struct_0(D_358)) | ~m1_pre_topc(D_358, C_361) | ~m1_subset_1(E_360, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_361), u1_struct_0(B_359)))) | ~v1_funct_2(E_360, u1_struct_0(C_361), u1_struct_0(B_359)) | ~v1_funct_1(E_360) | ~m1_pre_topc(D_358, A_357) | ~m1_pre_topc(C_361, A_357) | ~l1_pre_topc(B_359) | ~v2_pre_topc(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357))), inference(cnfTransformation, [status(thm)], [f_136])).
% 20.86/11.95  tff(c_1701, plain, (![A_357, B_359, D_358, E_360]: (k3_tmap_1(A_357, B_359, '#skF_4', D_358, E_360)=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_359), E_360, u1_struct_0(D_358)) | ~m1_pre_topc(D_358, '#skF_4') | ~m1_subset_1(E_360, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_359)))) | ~v1_funct_2(E_360, u1_struct_0('#skF_4'), u1_struct_0(B_359)) | ~v1_funct_1(E_360) | ~m1_pre_topc(D_358, A_357) | ~m1_pre_topc('#skF_4', A_357) | ~l1_pre_topc(B_359) | ~v2_pre_topc(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357))), inference(superposition, [status(thm), theory('equality')], [c_144, c_1695])).
% 20.86/11.95  tff(c_25155, plain, (![A_861, B_862, D_863, E_864]: (k3_tmap_1(A_861, B_862, '#skF_4', D_863, E_864)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_862), E_864, u1_struct_0(D_863)) | ~m1_pre_topc(D_863, '#skF_4') | ~m1_subset_1(E_864, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_862)))) | ~v1_funct_2(E_864, k2_struct_0('#skF_4'), u1_struct_0(B_862)) | ~v1_funct_1(E_864) | ~m1_pre_topc(D_863, A_861) | ~m1_pre_topc('#skF_4', A_861) | ~l1_pre_topc(B_862) | ~v2_pre_topc(B_862) | v2_struct_0(B_862) | ~l1_pre_topc(A_861) | ~v2_pre_topc(A_861) | v2_struct_0(A_861))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_144, c_1701])).
% 20.86/11.95  tff(c_25161, plain, (![A_861, D_863, E_864]: (k3_tmap_1(A_861, '#skF_2', '#skF_4', D_863, E_864)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), E_864, u1_struct_0(D_863)) | ~m1_pre_topc(D_863, '#skF_4') | ~m1_subset_1(E_864, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_864, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_864) | ~m1_pre_topc(D_863, A_861) | ~m1_pre_topc('#skF_4', A_861) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_861) | ~v2_pre_topc(A_861) | v2_struct_0(A_861))), inference(superposition, [status(thm), theory('equality')], [c_114, c_25155])).
% 20.86/11.95  tff(c_25171, plain, (![A_861, D_863, E_864]: (k3_tmap_1(A_861, '#skF_2', '#skF_4', D_863, E_864)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_864, u1_struct_0(D_863)) | ~m1_pre_topc(D_863, '#skF_4') | ~m1_subset_1(E_864, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_864, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_864) | ~m1_pre_topc(D_863, A_861) | ~m1_pre_topc('#skF_4', A_861) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_861) | ~v2_pre_topc(A_861) | v2_struct_0(A_861))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_114, c_114, c_25161])).
% 20.86/11.95  tff(c_42403, plain, (![A_1144, D_1145, E_1146]: (k3_tmap_1(A_1144, '#skF_2', '#skF_4', D_1145, E_1146)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_1146, u1_struct_0(D_1145)) | ~m1_pre_topc(D_1145, '#skF_4') | ~m1_subset_1(E_1146, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_1146, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_1146) | ~m1_pre_topc(D_1145, A_1144) | ~m1_pre_topc('#skF_4', A_1144) | ~l1_pre_topc(A_1144) | ~v2_pre_topc(A_1144) | v2_struct_0(A_1144))), inference(negUnitSimplification, [status(thm)], [c_80, c_25171])).
% 20.86/11.95  tff(c_42405, plain, (![A_1144, D_1145]: (k3_tmap_1(A_1144, '#skF_2', '#skF_4', D_1145, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_1145)) | ~m1_pre_topc(D_1145, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_1145, A_1144) | ~m1_pre_topc('#skF_4', A_1144) | ~l1_pre_topc(A_1144) | ~v2_pre_topc(A_1144) | v2_struct_0(A_1144))), inference(resolution, [status(thm)], [c_155, c_42403])).
% 20.86/11.95  tff(c_42409, plain, (![A_1147, D_1148]: (k3_tmap_1(A_1147, '#skF_2', '#skF_4', D_1148, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_1148)) | ~m1_pre_topc(D_1148, '#skF_4') | ~m1_pre_topc(D_1148, A_1147) | ~m1_pre_topc('#skF_4', A_1147) | ~l1_pre_topc(A_1147) | ~v2_pre_topc(A_1147) | v2_struct_0(A_1147))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_149, c_42405])).
% 20.86/11.95  tff(c_42525, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_42409])).
% 20.86/11.95  tff(c_42660, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_68, c_563, c_7098, c_615, c_42525])).
% 20.86/11.95  tff(c_42661, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_86, c_42660])).
% 20.86/11.95  tff(c_54, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_52, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_88, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 20.86/11.95  tff(c_42674, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42661, c_88])).
% 20.86/11.95  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_299])).
% 20.86/11.95  tff(c_22, plain, (![A_17]: (v3_pre_topc(k2_struct_0(A_17), A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.86/11.95  tff(c_38, plain, (![B_80, A_78]: (m1_subset_1(u1_struct_0(B_80), k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_pre_topc(B_80, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_185])).
% 20.86/11.95  tff(c_944, plain, (![B_319, A_320]: (v1_tsep_1(B_319, A_320) | ~v3_pre_topc(u1_struct_0(B_319), A_320) | ~m1_subset_1(u1_struct_0(B_319), k1_zfmisc_1(u1_struct_0(A_320))) | ~m1_pre_topc(B_319, A_320) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_154])).
% 20.86/11.95  tff(c_2114, plain, (![B_387, A_388]: (v1_tsep_1(B_387, A_388) | ~v3_pre_topc(u1_struct_0(B_387), A_388) | ~v2_pre_topc(A_388) | ~m1_pre_topc(B_387, A_388) | ~l1_pre_topc(A_388))), inference(resolution, [status(thm)], [c_38, c_944])).
% 20.86/11.95  tff(c_2677, plain, (![A_417]: (v1_tsep_1('#skF_3', A_417) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_417) | ~v2_pre_topc(A_417) | ~m1_pre_topc('#skF_3', A_417) | ~l1_pre_topc(A_417))), inference(superposition, [status(thm), theory('equality')], [c_615, c_2114])).
% 20.86/11.95  tff(c_2687, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_2677])).
% 20.86/11.95  tff(c_2694, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_137, c_563, c_2687])).
% 20.86/11.95  tff(c_7083, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_615, c_7074])).
% 20.86/11.95  tff(c_7096, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_563, c_7083])).
% 20.86/11.95  tff(c_7103, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7098, c_7096])).
% 20.86/11.95  tff(c_44, plain, (![A_85, D_141, C_133, F_147, B_117]: (r1_tmap_1(B_117, A_85, C_133, F_147) | ~r1_tmap_1(D_141, A_85, k2_tmap_1(B_117, A_85, C_133, D_141), F_147) | ~m1_subset_1(F_147, u1_struct_0(D_141)) | ~m1_subset_1(F_147, u1_struct_0(B_117)) | ~m1_pre_topc(D_141, B_117) | ~v1_tsep_1(D_141, B_117) | v2_struct_0(D_141) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_117), u1_struct_0(A_85)))) | ~v1_funct_2(C_133, u1_struct_0(B_117), u1_struct_0(A_85)) | ~v1_funct_1(C_133) | ~l1_pre_topc(B_117) | ~v2_pre_topc(B_117) | v2_struct_0(B_117) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_238])).
% 20.86/11.95  tff(c_7110, plain, (![F_147]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_147) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_147) | ~m1_subset_1(F_147, u1_struct_0('#skF_3')) | ~m1_subset_1(F_147, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7103, c_44])).
% 20.86/11.95  tff(c_7114, plain, (![F_147]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_147) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_147) | ~m1_subset_1(F_147, k2_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_187, c_137, c_66, c_149, c_114, c_144, c_155, c_114, c_144, c_2694, c_563, c_144, c_615, c_7110])).
% 20.86/11.95  tff(c_7115, plain, (![F_147]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_147) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_147) | ~m1_subset_1(F_147, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_70, c_74, c_7114])).
% 20.86/11.95  tff(c_42919, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42674, c_7115])).
% 20.86/11.95  tff(c_42925, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_42919])).
% 20.86/11.95  tff(c_42927, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42925])).
% 20.86/11.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.86/11.95  
% 20.86/11.95  Inference rules
% 20.86/11.95  ----------------------
% 20.86/11.95  #Ref     : 0
% 20.86/11.95  #Sup     : 9200
% 20.86/11.95  #Fact    : 0
% 20.86/11.95  #Define  : 0
% 20.86/11.95  #Split   : 25
% 20.86/11.95  #Chain   : 0
% 20.86/11.95  #Close   : 0
% 20.86/11.95  
% 20.86/11.95  Ordering : KBO
% 20.86/11.95  
% 20.86/11.95  Simplification rules
% 20.86/11.95  ----------------------
% 20.86/11.95  #Subsume      : 5338
% 20.86/11.95  #Demod        : 20388
% 20.86/11.95  #Tautology    : 1508
% 20.86/11.95  #SimpNegUnit  : 801
% 20.86/11.95  #BackRed      : 14
% 20.86/11.95  
% 20.86/11.95  #Partial instantiations: 0
% 20.86/11.95  #Strategies tried      : 1
% 20.86/11.95  
% 20.86/11.95  Timing (in seconds)
% 20.86/11.95  ----------------------
% 20.86/11.96  Preprocessing        : 0.43
% 20.86/11.96  Parsing              : 0.22
% 20.86/11.96  CNF conversion       : 0.05
% 20.86/11.96  Main loop            : 10.74
% 20.86/11.96  Inferencing          : 1.43
% 20.86/11.96  Reduction            : 3.40
% 20.86/11.96  Demodulation         : 2.63
% 20.86/11.96  BG Simplification    : 0.12
% 20.86/11.96  Subsumption          : 5.43
% 20.86/11.96  Abstraction          : 0.34
% 20.86/11.96  MUC search           : 0.00
% 20.86/11.96  Cooper               : 0.00
% 20.86/11.96  Total                : 11.22
% 20.86/11.96  Index Insertion      : 0.00
% 20.86/11.96  Index Deletion       : 0.00
% 20.86/11.96  Index Matching       : 0.00
% 20.86/11.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
