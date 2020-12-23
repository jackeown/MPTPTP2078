%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:42 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  142 (1227 expanded)
%              Number of leaves         :   44 ( 443 expanded)
%              Depth                    :   17
%              Number of atoms          :  283 (5630 expanded)
%              Number of equality atoms :   13 ( 630 expanded)
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

tff(f_224,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_102,axiom,(
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

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_175,axiom,(
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

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_110,plain,(
    ! [B_414,A_415] :
      ( l1_pre_topc(B_414)
      | ~ m1_pre_topc(B_414,A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_119,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_110])).

tff(c_126,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_119])).

tff(c_14,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_87,plain,(
    ! [A_412] :
      ( u1_struct_0(A_412) = k2_struct_0(A_412)
      | ~ l1_struct_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,(
    ! [A_12] :
      ( u1_struct_0(A_12) = k2_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_135,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_91])).

tff(c_159,plain,(
    ! [A_420] :
      ( ~ v1_xboole_0(u1_struct_0(A_420))
      | ~ l1_struct_0(A_420)
      | v2_struct_0(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_162,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_159])).

tff(c_172,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_162])).

tff(c_176,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_179,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_179])).

tff(c_184,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_145,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_46])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_252,plain,(
    ! [B_424,A_425] :
      ( v2_pre_topc(B_424)
      | ~ m1_pre_topc(B_424,A_425)
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_261,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_252])).

tff(c_268,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_261])).

tff(c_26,plain,(
    ! [A_23] :
      ( v3_pre_topc(k2_struct_0(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    ! [A_27] :
      ( m1_pre_topc(A_27,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_280,plain,(
    ! [B_432,A_433] :
      ( m1_subset_1(u1_struct_0(B_432),k1_zfmisc_1(u1_struct_0(A_433)))
      | ~ m1_pre_topc(B_432,A_433)
      | ~ l1_pre_topc(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_291,plain,(
    ! [B_432] :
      ( m1_subset_1(u1_struct_0(B_432),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_432,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_280])).

tff(c_320,plain,(
    ! [B_434] :
      ( m1_subset_1(u1_struct_0(B_434),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_434,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_291])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_340,plain,(
    ! [B_435] :
      ( r1_tarski(u1_struct_0(B_435),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_435,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_320,c_4])).

tff(c_343,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_340])).

tff(c_353,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_357,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_353])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_357])).

tff(c_363,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_116,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_110])).

tff(c_123,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_116])).

tff(c_131,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_91])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_136,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_48])).

tff(c_678,plain,(
    ! [B_451,A_452] :
      ( m1_pre_topc(B_451,A_452)
      | ~ m1_pre_topc(B_451,g1_pre_topc(u1_struct_0(A_452),u1_pre_topc(A_452)))
      | ~ l1_pre_topc(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_684,plain,(
    ! [B_451] :
      ( m1_pre_topc(B_451,'#skF_3')
      | ~ m1_pre_topc(B_451,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_678])).

tff(c_698,plain,(
    ! [B_451] :
      ( m1_pre_topc(B_451,'#skF_3')
      | ~ m1_pre_topc(B_451,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_136,c_684])).

tff(c_297,plain,(
    ! [B_432] :
      ( m1_subset_1(u1_struct_0(B_432),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_432,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_280])).

tff(c_977,plain,(
    ! [B_470] :
      ( m1_subset_1(u1_struct_0(B_470),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_470,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_297])).

tff(c_997,plain,(
    ! [B_471] :
      ( r1_tarski(u1_struct_0(B_471),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_471,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_977,c_4])).

tff(c_1000,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_997])).

tff(c_1010,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1013,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_698,c_1010])).

tff(c_1017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_1013])).

tff(c_1018,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_328,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_320])).

tff(c_1443,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_328])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_92,plain,(
    ! [A_413] :
      ( u1_struct_0(A_413) = k2_struct_0(A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(resolution,[status(thm)],[c_14,c_87])).

tff(c_100,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_105,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_52])).

tff(c_144,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_105])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_142,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_50])).

tff(c_143,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_142])).

tff(c_346,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_340])).

tff(c_376,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_567,plain,(
    ! [A_447,B_448] :
      ( m1_pre_topc(A_447,g1_pre_topc(u1_struct_0(B_448),u1_pre_topc(B_448)))
      | ~ m1_pre_topc(A_447,B_448)
      | ~ l1_pre_topc(B_448)
      | ~ l1_pre_topc(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_584,plain,(
    ! [A_447] :
      ( m1_pre_topc(A_447,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_447,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_447) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_567])).

tff(c_603,plain,(
    ! [A_449] :
      ( m1_pre_topc(A_449,'#skF_4')
      | ~ m1_pre_topc(A_449,'#skF_3')
      | ~ l1_pre_topc(A_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_136,c_584])).

tff(c_617,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_603])).

tff(c_628,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_617])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_628])).

tff(c_632,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_42,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_75,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_137,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_75])).

tff(c_40,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_76,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_1091,plain,(
    ! [E_488,B_486,D_491,H_489,A_485,C_490,F_487] :
      ( r1_tmap_1(D_491,B_486,E_488,H_489)
      | ~ r1_tmap_1(C_490,B_486,k3_tmap_1(A_485,B_486,D_491,C_490,E_488),H_489)
      | ~ r1_tarski(F_487,u1_struct_0(C_490))
      | ~ r2_hidden(H_489,F_487)
      | ~ v3_pre_topc(F_487,D_491)
      | ~ m1_subset_1(H_489,u1_struct_0(C_490))
      | ~ m1_subset_1(H_489,u1_struct_0(D_491))
      | ~ m1_subset_1(F_487,k1_zfmisc_1(u1_struct_0(D_491)))
      | ~ m1_pre_topc(C_490,D_491)
      | ~ m1_subset_1(E_488,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_491),u1_struct_0(B_486))))
      | ~ v1_funct_2(E_488,u1_struct_0(D_491),u1_struct_0(B_486))
      | ~ v1_funct_1(E_488)
      | ~ m1_pre_topc(D_491,A_485)
      | v2_struct_0(D_491)
      | ~ m1_pre_topc(C_490,A_485)
      | v2_struct_0(C_490)
      | ~ l1_pre_topc(B_486)
      | ~ v2_pre_topc(B_486)
      | v2_struct_0(B_486)
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1093,plain,(
    ! [F_487] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_487,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_487)
      | ~ v3_pre_topc(F_487,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_487,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_76,c_1091])).

tff(c_1096,plain,(
    ! [F_487] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_487,k2_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_487)
      | ~ v3_pre_topc(F_487,'#skF_4')
      | ~ m1_subset_1(F_487,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_144,c_100,c_135,c_143,c_100,c_135,c_632,c_135,c_145,c_135,c_137,c_131,c_131,c_1093])).

tff(c_1097,plain,(
    ! [F_487] :
      ( ~ r1_tarski(F_487,k2_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_487)
      | ~ v3_pre_topc(F_487,'#skF_4')
      | ~ m1_subset_1(F_487,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_38,c_1096])).

tff(c_1446,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1443,c_1097])).

tff(c_1454,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1446])).

tff(c_1462,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1454])).

tff(c_1465,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1462])).

tff(c_1469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_126,c_1465])).

tff(c_1470,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1454])).

tff(c_1474,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_1470])).

tff(c_1477,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1474])).

tff(c_1479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_184,c_1477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.72  
% 4.08/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.72  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.08/1.72  
% 4.08/1.72  %Foreground sorts:
% 4.08/1.72  
% 4.08/1.72  
% 4.08/1.72  %Background operators:
% 4.08/1.72  
% 4.08/1.72  
% 4.08/1.72  %Foreground operators:
% 4.08/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.08/1.72  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.08/1.72  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.08/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.08/1.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.08/1.72  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.08/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.08/1.72  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.08/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.08/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.08/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.08/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.08/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.08/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.08/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.08/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.08/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.08/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.08/1.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.08/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.08/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.08/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.08/1.72  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.08/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.08/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.08/1.72  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.08/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.08/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.08/1.72  
% 4.08/1.75  tff(f_224, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.08/1.75  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.08/1.75  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.08/1.75  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.08/1.75  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.08/1.75  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.08/1.75  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.08/1.75  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.08/1.75  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.08/1.75  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.08/1.75  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.08/1.75  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.08/1.75  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.08/1.75  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.08/1.75  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_110, plain, (![B_414, A_415]: (l1_pre_topc(B_414) | ~m1_pre_topc(B_414, A_415) | ~l1_pre_topc(A_415))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.08/1.75  tff(c_119, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_110])).
% 4.08/1.75  tff(c_126, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_119])).
% 4.08/1.75  tff(c_14, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.08/1.75  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_87, plain, (![A_412]: (u1_struct_0(A_412)=k2_struct_0(A_412) | ~l1_struct_0(A_412))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.75  tff(c_91, plain, (![A_12]: (u1_struct_0(A_12)=k2_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_14, c_87])).
% 4.08/1.75  tff(c_135, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_126, c_91])).
% 4.08/1.75  tff(c_159, plain, (![A_420]: (~v1_xboole_0(u1_struct_0(A_420)) | ~l1_struct_0(A_420) | v2_struct_0(A_420))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.08/1.75  tff(c_162, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_159])).
% 4.08/1.75  tff(c_172, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_162])).
% 4.08/1.75  tff(c_176, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_172])).
% 4.08/1.75  tff(c_179, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_176])).
% 4.08/1.75  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_179])).
% 4.08/1.75  tff(c_184, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_172])).
% 4.08/1.75  tff(c_46, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_145, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_46])).
% 4.08/1.75  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.75  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_252, plain, (![B_424, A_425]: (v2_pre_topc(B_424) | ~m1_pre_topc(B_424, A_425) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.08/1.75  tff(c_261, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_252])).
% 4.08/1.75  tff(c_268, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_261])).
% 4.08/1.75  tff(c_26, plain, (![A_23]: (v3_pre_topc(k2_struct_0(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.08/1.75  tff(c_30, plain, (![A_27]: (m1_pre_topc(A_27, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.08/1.75  tff(c_280, plain, (![B_432, A_433]: (m1_subset_1(u1_struct_0(B_432), k1_zfmisc_1(u1_struct_0(A_433))) | ~m1_pre_topc(B_432, A_433) | ~l1_pre_topc(A_433))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.08/1.75  tff(c_291, plain, (![B_432]: (m1_subset_1(u1_struct_0(B_432), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_432, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_280])).
% 4.08/1.75  tff(c_320, plain, (![B_434]: (m1_subset_1(u1_struct_0(B_434), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_434, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_291])).
% 4.08/1.75  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.08/1.75  tff(c_340, plain, (![B_435]: (r1_tarski(u1_struct_0(B_435), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_435, '#skF_4'))), inference(resolution, [status(thm)], [c_320, c_4])).
% 4.08/1.75  tff(c_343, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_340])).
% 4.08/1.75  tff(c_353, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_343])).
% 4.08/1.75  tff(c_357, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_353])).
% 4.08/1.75  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_357])).
% 4.08/1.75  tff(c_363, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_343])).
% 4.08/1.75  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_116, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_110])).
% 4.08/1.75  tff(c_123, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_116])).
% 4.08/1.75  tff(c_131, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_123, c_91])).
% 4.08/1.75  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_136, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_48])).
% 4.08/1.75  tff(c_678, plain, (![B_451, A_452]: (m1_pre_topc(B_451, A_452) | ~m1_pre_topc(B_451, g1_pre_topc(u1_struct_0(A_452), u1_pre_topc(A_452))) | ~l1_pre_topc(A_452))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.08/1.75  tff(c_684, plain, (![B_451]: (m1_pre_topc(B_451, '#skF_3') | ~m1_pre_topc(B_451, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_678])).
% 4.08/1.75  tff(c_698, plain, (![B_451]: (m1_pre_topc(B_451, '#skF_3') | ~m1_pre_topc(B_451, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_136, c_684])).
% 4.08/1.75  tff(c_297, plain, (![B_432]: (m1_subset_1(u1_struct_0(B_432), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_432, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_280])).
% 4.08/1.75  tff(c_977, plain, (![B_470]: (m1_subset_1(u1_struct_0(B_470), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_470, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_297])).
% 4.08/1.75  tff(c_997, plain, (![B_471]: (r1_tarski(u1_struct_0(B_471), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_471, '#skF_3'))), inference(resolution, [status(thm)], [c_977, c_4])).
% 4.08/1.75  tff(c_1000, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_135, c_997])).
% 4.08/1.75  tff(c_1010, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_1000])).
% 4.08/1.75  tff(c_1013, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_698, c_1010])).
% 4.08/1.75  tff(c_1017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_363, c_1013])).
% 4.08/1.75  tff(c_1018, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1000])).
% 4.08/1.75  tff(c_328, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_320])).
% 4.08/1.75  tff(c_1443, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_328])).
% 4.08/1.75  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_38, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_92, plain, (![A_413]: (u1_struct_0(A_413)=k2_struct_0(A_413) | ~l1_pre_topc(A_413))), inference(resolution, [status(thm)], [c_14, c_87])).
% 4.08/1.75  tff(c_100, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_92])).
% 4.08/1.75  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_105, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_52])).
% 4.08/1.75  tff(c_144, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_105])).
% 4.08/1.75  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_142, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_50])).
% 4.08/1.75  tff(c_143, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_142])).
% 4.08/1.75  tff(c_346, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_131, c_340])).
% 4.08/1.75  tff(c_376, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_346])).
% 4.08/1.75  tff(c_567, plain, (![A_447, B_448]: (m1_pre_topc(A_447, g1_pre_topc(u1_struct_0(B_448), u1_pre_topc(B_448))) | ~m1_pre_topc(A_447, B_448) | ~l1_pre_topc(B_448) | ~l1_pre_topc(A_447))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.08/1.75  tff(c_584, plain, (![A_447]: (m1_pre_topc(A_447, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_447, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_447))), inference(superposition, [status(thm), theory('equality')], [c_131, c_567])).
% 4.08/1.75  tff(c_603, plain, (![A_449]: (m1_pre_topc(A_449, '#skF_4') | ~m1_pre_topc(A_449, '#skF_3') | ~l1_pre_topc(A_449))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_136, c_584])).
% 4.08/1.75  tff(c_617, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_603])).
% 4.08/1.75  tff(c_628, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_617])).
% 4.08/1.75  tff(c_630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_628])).
% 4.08/1.75  tff(c_632, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_346])).
% 4.08/1.75  tff(c_42, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_75, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 4.08/1.75  tff(c_137, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_75])).
% 4.08/1.75  tff(c_40, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.08/1.75  tff(c_76, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 4.08/1.75  tff(c_1091, plain, (![E_488, B_486, D_491, H_489, A_485, C_490, F_487]: (r1_tmap_1(D_491, B_486, E_488, H_489) | ~r1_tmap_1(C_490, B_486, k3_tmap_1(A_485, B_486, D_491, C_490, E_488), H_489) | ~r1_tarski(F_487, u1_struct_0(C_490)) | ~r2_hidden(H_489, F_487) | ~v3_pre_topc(F_487, D_491) | ~m1_subset_1(H_489, u1_struct_0(C_490)) | ~m1_subset_1(H_489, u1_struct_0(D_491)) | ~m1_subset_1(F_487, k1_zfmisc_1(u1_struct_0(D_491))) | ~m1_pre_topc(C_490, D_491) | ~m1_subset_1(E_488, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_491), u1_struct_0(B_486)))) | ~v1_funct_2(E_488, u1_struct_0(D_491), u1_struct_0(B_486)) | ~v1_funct_1(E_488) | ~m1_pre_topc(D_491, A_485) | v2_struct_0(D_491) | ~m1_pre_topc(C_490, A_485) | v2_struct_0(C_490) | ~l1_pre_topc(B_486) | ~v2_pre_topc(B_486) | v2_struct_0(B_486) | ~l1_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.08/1.75  tff(c_1093, plain, (![F_487]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_487, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_487) | ~v3_pre_topc(F_487, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_487, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_76, c_1091])).
% 4.08/1.75  tff(c_1096, plain, (![F_487]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_487, k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_487) | ~v3_pre_topc(F_487, '#skF_4') | ~m1_subset_1(F_487, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_144, c_100, c_135, c_143, c_100, c_135, c_632, c_135, c_145, c_135, c_137, c_131, c_131, c_1093])).
% 4.08/1.75  tff(c_1097, plain, (![F_487]: (~r1_tarski(F_487, k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_487) | ~v3_pre_topc(F_487, '#skF_4') | ~m1_subset_1(F_487, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_38, c_1096])).
% 4.08/1.75  tff(c_1446, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1443, c_1097])).
% 4.08/1.75  tff(c_1454, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1446])).
% 4.08/1.75  tff(c_1462, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1454])).
% 4.08/1.75  tff(c_1465, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1462])).
% 4.08/1.75  tff(c_1469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_268, c_126, c_1465])).
% 4.08/1.75  tff(c_1470, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1454])).
% 4.08/1.75  tff(c_1474, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2, c_1470])).
% 4.08/1.75  tff(c_1477, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_1474])).
% 4.08/1.75  tff(c_1479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_184, c_1477])).
% 4.08/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.08/1.75  
% 4.08/1.75  Inference rules
% 4.08/1.75  ----------------------
% 4.08/1.75  #Ref     : 0
% 4.08/1.75  #Sup     : 289
% 4.08/1.75  #Fact    : 0
% 4.08/1.75  #Define  : 0
% 4.08/1.75  #Split   : 25
% 4.08/1.75  #Chain   : 0
% 4.08/1.75  #Close   : 0
% 4.08/1.75  
% 4.08/1.75  Ordering : KBO
% 4.08/1.75  
% 4.08/1.75  Simplification rules
% 4.08/1.75  ----------------------
% 4.08/1.75  #Subsume      : 30
% 4.08/1.75  #Demod        : 239
% 4.08/1.75  #Tautology    : 87
% 4.08/1.75  #SimpNegUnit  : 19
% 4.08/1.75  #BackRed      : 6
% 4.08/1.75  
% 4.08/1.75  #Partial instantiations: 0
% 4.08/1.75  #Strategies tried      : 1
% 4.08/1.75  
% 4.08/1.75  Timing (in seconds)
% 4.08/1.75  ----------------------
% 4.08/1.75  Preprocessing        : 0.39
% 4.08/1.75  Parsing              : 0.20
% 4.08/1.75  CNF conversion       : 0.06
% 4.08/1.75  Main loop            : 0.53
% 4.08/1.75  Inferencing          : 0.18
% 4.08/1.75  Reduction            : 0.18
% 4.08/1.75  Demodulation         : 0.13
% 4.08/1.75  BG Simplification    : 0.03
% 4.08/1.75  Subsumption          : 0.10
% 4.08/1.75  Abstraction          : 0.02
% 4.08/1.75  MUC search           : 0.00
% 4.08/1.75  Cooper               : 0.00
% 4.08/1.75  Total                : 0.97
% 4.08/1.75  Index Insertion      : 0.00
% 4.08/1.75  Index Deletion       : 0.00
% 4.08/1.75  Index Matching       : 0.00
% 4.08/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
