%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:42 EST 2020

% Result     : Theorem 16.20s
% Output     : CNFRefutation 16.20s
% Verified   : 
% Statistics : Number of formulae       :  157 (1298 expanded)
%              Number of leaves         :   44 ( 467 expanded)
%              Depth                    :   15
%              Number of atoms          :  434 (6165 expanded)
%              Number of equality atoms :   33 ( 690 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_286,negated_conjecture,(
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

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_175,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_160,axiom,(
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
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_237,axiom,(
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

tff(f_109,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_114,plain,(
    ! [B_319,A_320] :
      ( l1_pre_topc(B_319)
      | ~ m1_pre_topc(B_319,A_320)
      | ~ l1_pre_topc(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_120,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_114])).

tff(c_126,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_120])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_90,plain,(
    ! [A_317] :
      ( u1_struct_0(A_317) = k2_struct_0(A_317)
      | ~ l1_struct_0(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_135,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_94])).

tff(c_95,plain,(
    ! [A_318] :
      ( u1_struct_0(A_318) = k2_struct_0(A_318)
      | ~ l1_pre_topc(A_318) ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_103,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_95])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_109,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_56])).

tff(c_146,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_109])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54])).

tff(c_152,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_108])).

tff(c_117,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_114])).

tff(c_123,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_117])).

tff(c_131,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_94])).

tff(c_177,plain,(
    ! [B_326,A_327] :
      ( m1_subset_1(u1_struct_0(B_326),k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ m1_pre_topc(B_326,A_327)
      | ~ l1_pre_topc(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_183,plain,(
    ! [B_326] :
      ( m1_subset_1(u1_struct_0(B_326),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_326,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_177])).

tff(c_210,plain,(
    ! [B_328] :
      ( m1_subset_1(u1_struct_0(B_328),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_328,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_183])).

tff(c_216,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_210])).

tff(c_1831,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_153,plain,(
    ! [B_322,A_323] :
      ( v2_pre_topc(B_322)
      | ~ m1_pre_topc(B_322,A_323)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_156,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_153])).

tff(c_162,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_156])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_136,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_52])).

tff(c_1087,plain,(
    ! [A_379,B_380] :
      ( k1_tsep_1(A_379,B_380,B_380) = g1_pre_topc(u1_struct_0(B_380),u1_pre_topc(B_380))
      | ~ m1_pre_topc(B_380,A_379)
      | v2_struct_0(B_380)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1099,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_1087])).

tff(c_1119,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_136,c_131,c_1099])).

tff(c_1120,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_1119])).

tff(c_1609,plain,(
    ! [B_405,C_406,A_407] :
      ( m1_pre_topc(B_405,C_406)
      | k1_tsep_1(A_407,B_405,C_406) != g1_pre_topc(u1_struct_0(C_406),u1_pre_topc(C_406))
      | ~ m1_pre_topc(C_406,A_407)
      | v2_struct_0(C_406)
      | ~ m1_pre_topc(B_405,A_407)
      | v2_struct_0(B_405)
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407)
      | v2_struct_0(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1615,plain,(
    ! [B_405,A_407] :
      ( m1_pre_topc(B_405,'#skF_3')
      | k1_tsep_1(A_407,B_405,'#skF_3') != g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_407)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_405,A_407)
      | v2_struct_0(B_405)
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407)
      | v2_struct_0(A_407) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_1609])).

tff(c_1623,plain,(
    ! [B_405,A_407] :
      ( m1_pre_topc(B_405,'#skF_3')
      | k1_tsep_1(A_407,B_405,'#skF_3') != '#skF_4'
      | ~ m1_pre_topc('#skF_3',A_407)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_405,A_407)
      | v2_struct_0(B_405)
      | ~ l1_pre_topc(A_407)
      | ~ v2_pre_topc(A_407)
      | v2_struct_0(A_407) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_1615])).

tff(c_1648,plain,(
    ! [B_411,A_412] :
      ( m1_pre_topc(B_411,'#skF_3')
      | k1_tsep_1(A_412,B_411,'#skF_3') != '#skF_4'
      | ~ m1_pre_topc('#skF_3',A_412)
      | ~ m1_pre_topc(B_411,A_412)
      | v2_struct_0(B_411)
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1623])).

tff(c_1657,plain,(
    ! [B_411] :
      ( m1_pre_topc(B_411,'#skF_3')
      | k1_tsep_1('#skF_1',B_411,'#skF_3') != '#skF_4'
      | ~ m1_pre_topc(B_411,'#skF_1')
      | v2_struct_0(B_411)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_64,c_1648])).

tff(c_1668,plain,(
    ! [B_411] :
      ( m1_pre_topc(B_411,'#skF_3')
      | k1_tsep_1('#skF_1',B_411,'#skF_3') != '#skF_4'
      | ~ m1_pre_topc(B_411,'#skF_1')
      | v2_struct_0(B_411)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1657])).

tff(c_1670,plain,(
    ! [B_413] :
      ( m1_pre_topc(B_413,'#skF_3')
      | k1_tsep_1('#skF_1',B_413,'#skF_3') != '#skF_4'
      | ~ m1_pre_topc(B_413,'#skF_1')
      | v2_struct_0(B_413) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1668])).

tff(c_189,plain,(
    ! [B_326] :
      ( m1_subset_1(u1_struct_0(B_326),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_326,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_177])).

tff(c_223,plain,(
    ! [B_329] :
      ( m1_subset_1(u1_struct_0(B_329),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_329,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_189])).

tff(c_229,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_223])).

tff(c_335,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_1701,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') != '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1670,c_335])).

tff(c_1758,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1120,c_1701])).

tff(c_1760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1758])).

tff(c_1762,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_2073,plain,(
    ! [A_430,B_431] :
      ( k1_tsep_1(A_430,B_431,B_431) = g1_pre_topc(u1_struct_0(B_431),u1_pre_topc(B_431))
      | ~ m1_pre_topc(B_431,A_430)
      | v2_struct_0(B_431)
      | ~ l1_pre_topc(A_430)
      | ~ v2_pre_topc(A_430)
      | v2_struct_0(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2077,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_3','#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1762,c_2073])).

tff(c_2090,plain,
    ( k1_tsep_1('#skF_3','#skF_3','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_123,c_136,c_131,c_2077])).

tff(c_2091,plain,(
    k1_tsep_1('#skF_3','#skF_3','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2090])).

tff(c_2300,plain,(
    ! [B_441,A_442,C_443] :
      ( m1_pre_topc(B_441,k1_tsep_1(A_442,B_441,C_443))
      | ~ m1_pre_topc(C_443,A_442)
      | v2_struct_0(C_443)
      | ~ m1_pre_topc(B_441,A_442)
      | v2_struct_0(B_441)
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2334,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2091,c_2300])).

tff(c_2356,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_123,c_1762,c_1762,c_2334])).

tff(c_2358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1831,c_2356])).

tff(c_2360,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_147,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_50])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_79,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_137,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_79])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_3747,plain,(
    ! [G_502,A_497,C_498,B_499,D_501,E_500] :
      ( r1_tmap_1(D_501,B_499,E_500,G_502)
      | ~ r1_tmap_1(C_498,B_499,k3_tmap_1(A_497,B_499,D_501,C_498,E_500),G_502)
      | ~ m1_subset_1(G_502,u1_struct_0(C_498))
      | ~ m1_subset_1(G_502,u1_struct_0(D_501))
      | ~ m1_pre_topc(C_498,D_501)
      | ~ v1_tsep_1(C_498,D_501)
      | ~ m1_subset_1(E_500,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_501),u1_struct_0(B_499))))
      | ~ v1_funct_2(E_500,u1_struct_0(D_501),u1_struct_0(B_499))
      | ~ v1_funct_1(E_500)
      | ~ m1_pre_topc(D_501,A_497)
      | v2_struct_0(D_501)
      | ~ m1_pre_topc(C_498,A_497)
      | v2_struct_0(C_498)
      | ~ l1_pre_topc(B_499)
      | ~ v2_pre_topc(B_499)
      | v2_struct_0(B_499)
      | ~ l1_pre_topc(A_497)
      | ~ v2_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_3749,plain,
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
    inference(resolution,[status(thm)],[c_80,c_3747])).

tff(c_3752,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_146,c_103,c_135,c_152,c_103,c_135,c_2360,c_147,c_135,c_137,c_131,c_3749])).

tff(c_3753,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_42,c_3752])).

tff(c_2359,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_159,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_153])).

tff(c_165,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_159])).

tff(c_2602,plain,(
    ! [B_452,A_453] :
      ( v1_tsep_1(B_452,A_453)
      | ~ v3_pre_topc(u1_struct_0(B_452),A_453)
      | ~ m1_subset_1(u1_struct_0(B_452),k1_zfmisc_1(u1_struct_0(A_453)))
      | ~ m1_pre_topc(B_452,A_453)
      | ~ l1_pre_topc(A_453)
      | ~ v2_pre_topc(A_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2611,plain,(
    ! [B_452] :
      ( v1_tsep_1(B_452,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_452),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_452),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_452,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_2602])).

tff(c_31147,plain,(
    ! [B_943] :
      ( v1_tsep_1(B_943,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_943),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_943),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_943,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_126,c_2611])).

tff(c_31171,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_31147])).

tff(c_31186,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_2359,c_131,c_31171])).

tff(c_31187,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3753,c_31186])).

tff(c_1761,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_12,plain,(
    ! [A_16] :
      ( v3_pre_topc(k2_struct_0(A_16),A_16)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [B_44,A_42] :
      ( m1_subset_1(u1_struct_0(B_44),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_pre_topc(B_44,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3217,plain,(
    ! [B_477,A_478] :
      ( v1_tsep_1(B_477,A_478)
      | ~ v3_pre_topc(u1_struct_0(B_477),A_478)
      | ~ v2_pre_topc(A_478)
      | ~ m1_pre_topc(B_477,A_478)
      | ~ l1_pre_topc(A_478) ) ),
    inference(resolution,[status(thm)],[c_26,c_2602])).

tff(c_3672,plain,(
    ! [A_492] :
      ( v1_tsep_1('#skF_3',A_492)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_492)
      | ~ v2_pre_topc(A_492)
      | ~ m1_pre_topc('#skF_3',A_492)
      | ~ l1_pre_topc(A_492) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_3217])).

tff(c_3676,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_3672])).

tff(c_3679,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_123,c_1762,c_3676])).

tff(c_2413,plain,(
    ! [B_444,A_445] :
      ( v3_pre_topc(u1_struct_0(B_444),A_445)
      | ~ v1_tsep_1(B_444,A_445)
      | ~ m1_subset_1(u1_struct_0(B_444),k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ m1_pre_topc(B_444,A_445)
      | ~ l1_pre_topc(A_445)
      | ~ v2_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2428,plain,(
    ! [B_444] :
      ( v3_pre_topc(u1_struct_0(B_444),'#skF_3')
      | ~ v1_tsep_1(B_444,'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_444),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_444,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_2413])).

tff(c_31406,plain,(
    ! [B_947] :
      ( v3_pre_topc(u1_struct_0(B_947),'#skF_3')
      | ~ v1_tsep_1(B_947,'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_947),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_947,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_123,c_2428])).

tff(c_31433,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_31406])).

tff(c_31449,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1762,c_1761,c_3679,c_131,c_31433])).

tff(c_236,plain,(
    ! [B_330,A_331] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_330),u1_pre_topc(B_330)),A_331)
      | ~ m1_pre_topc(B_330,A_331)
      | ~ l1_pre_topc(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_250,plain,(
    ! [A_331] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_331)
      | ~ m1_pre_topc('#skF_3',A_331)
      | ~ l1_pre_topc(A_331) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_236])).

tff(c_260,plain,(
    ! [A_331] :
      ( m1_pre_topc('#skF_4',A_331)
      | ~ m1_pre_topc('#skF_3',A_331)
      | ~ l1_pre_topc(A_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_250])).

tff(c_1767,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1762,c_260])).

tff(c_1779,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_1767])).

tff(c_2867,plain,(
    ! [D_462,C_463,A_464] :
      ( v3_pre_topc(D_462,C_463)
      | ~ m1_subset_1(D_462,k1_zfmisc_1(u1_struct_0(C_463)))
      | ~ v3_pre_topc(D_462,A_464)
      | ~ m1_pre_topc(C_463,A_464)
      | ~ m1_subset_1(D_462,k1_zfmisc_1(u1_struct_0(A_464)))
      | ~ l1_pre_topc(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4862,plain,(
    ! [B_538,A_539,A_540] :
      ( v3_pre_topc(u1_struct_0(B_538),A_539)
      | ~ v3_pre_topc(u1_struct_0(B_538),A_540)
      | ~ m1_pre_topc(A_539,A_540)
      | ~ m1_subset_1(u1_struct_0(B_538),k1_zfmisc_1(u1_struct_0(A_540)))
      | ~ l1_pre_topc(A_540)
      | ~ m1_pre_topc(B_538,A_539)
      | ~ l1_pre_topc(A_539) ) ),
    inference(resolution,[status(thm)],[c_26,c_2867])).

tff(c_4888,plain,(
    ! [B_538] :
      ( v3_pre_topc(u1_struct_0(B_538),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_538),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_538),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_538,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1779,c_4862])).

tff(c_35884,plain,(
    ! [B_1015] :
      ( v3_pre_topc(u1_struct_0(B_1015),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_1015),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_1015),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_1015,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_123,c_131,c_4888])).

tff(c_35911,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_35884])).

tff(c_35927,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2360,c_1761,c_31449,c_131,c_131,c_35911])).

tff(c_35929,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31187,c_35927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.20/7.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.20/7.84  
% 16.20/7.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.20/7.84  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.20/7.84  
% 16.20/7.84  %Foreground sorts:
% 16.20/7.84  
% 16.20/7.84  
% 16.20/7.84  %Background operators:
% 16.20/7.84  
% 16.20/7.84  
% 16.20/7.84  %Foreground operators:
% 16.20/7.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 16.20/7.84  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 16.20/7.84  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 16.20/7.84  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 16.20/7.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.20/7.84  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 16.20/7.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.20/7.84  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 16.20/7.84  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 16.20/7.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.20/7.84  tff('#skF_7', type, '#skF_7': $i).
% 16.20/7.84  tff('#skF_5', type, '#skF_5': $i).
% 16.20/7.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.20/7.84  tff('#skF_6', type, '#skF_6': $i).
% 16.20/7.84  tff('#skF_2', type, '#skF_2': $i).
% 16.20/7.84  tff('#skF_3', type, '#skF_3': $i).
% 16.20/7.84  tff('#skF_1', type, '#skF_1': $i).
% 16.20/7.84  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 16.20/7.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.20/7.84  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 16.20/7.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.20/7.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.20/7.84  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 16.20/7.84  tff('#skF_4', type, '#skF_4': $i).
% 16.20/7.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.20/7.84  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 16.20/7.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.20/7.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.20/7.84  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 16.20/7.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.20/7.84  
% 16.20/7.86  tff(f_286, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 16.20/7.86  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 16.20/7.86  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 16.20/7.86  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 16.20/7.86  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 16.20/7.86  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 16.20/7.86  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 16.20/7.86  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 16.20/7.86  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 16.20/7.86  tff(f_237, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 16.20/7.86  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 16.20/7.86  tff(f_65, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 16.20/7.86  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 16.20/7.86  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 16.20/7.86  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_114, plain, (![B_319, A_320]: (l1_pre_topc(B_319) | ~m1_pre_topc(B_319, A_320) | ~l1_pre_topc(A_320))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.20/7.86  tff(c_120, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_114])).
% 16.20/7.86  tff(c_126, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_120])).
% 16.20/7.86  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.20/7.86  tff(c_90, plain, (![A_317]: (u1_struct_0(A_317)=k2_struct_0(A_317) | ~l1_struct_0(A_317))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.20/7.86  tff(c_94, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_90])).
% 16.20/7.86  tff(c_135, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_126, c_94])).
% 16.20/7.86  tff(c_95, plain, (![A_318]: (u1_struct_0(A_318)=k2_struct_0(A_318) | ~l1_pre_topc(A_318))), inference(resolution, [status(thm)], [c_6, c_90])).
% 16.20/7.86  tff(c_103, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_95])).
% 16.20/7.86  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_109, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_56])).
% 16.20/7.86  tff(c_146, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_109])).
% 16.20/7.86  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.86  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_54])).
% 16.20/7.86  tff(c_152, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_108])).
% 16.20/7.86  tff(c_117, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_114])).
% 16.20/7.86  tff(c_123, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_117])).
% 16.20/7.86  tff(c_131, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_123, c_94])).
% 16.20/7.86  tff(c_177, plain, (![B_326, A_327]: (m1_subset_1(u1_struct_0(B_326), k1_zfmisc_1(u1_struct_0(A_327))) | ~m1_pre_topc(B_326, A_327) | ~l1_pre_topc(A_327))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.20/7.86  tff(c_183, plain, (![B_326]: (m1_subset_1(u1_struct_0(B_326), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_326, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_177])).
% 16.20/7.86  tff(c_210, plain, (![B_328]: (m1_subset_1(u1_struct_0(B_328), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_328, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_183])).
% 16.20/7.86  tff(c_216, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_131, c_210])).
% 16.20/7.86  tff(c_1831, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_216])).
% 16.20/7.86  tff(c_153, plain, (![B_322, A_323]: (v2_pre_topc(B_322) | ~m1_pre_topc(B_322, A_323) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_34])).
% 16.20/7.86  tff(c_156, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_153])).
% 16.20/7.87  tff(c_162, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_156])).
% 16.20/7.87  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.87  tff(c_136, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_52])).
% 16.20/7.87  tff(c_1087, plain, (![A_379, B_380]: (k1_tsep_1(A_379, B_380, B_380)=g1_pre_topc(u1_struct_0(B_380), u1_pre_topc(B_380)) | ~m1_pre_topc(B_380, A_379) | v2_struct_0(B_380) | ~l1_pre_topc(A_379) | ~v2_pre_topc(A_379) | v2_struct_0(A_379))), inference(cnfTransformation, [status(thm)], [f_175])).
% 16.20/7.87  tff(c_1099, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_1087])).
% 16.20/7.87  tff(c_1119, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4' | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_136, c_131, c_1099])).
% 16.20/7.87  tff(c_1120, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_1119])).
% 16.20/7.87  tff(c_1609, plain, (![B_405, C_406, A_407]: (m1_pre_topc(B_405, C_406) | k1_tsep_1(A_407, B_405, C_406)!=g1_pre_topc(u1_struct_0(C_406), u1_pre_topc(C_406)) | ~m1_pre_topc(C_406, A_407) | v2_struct_0(C_406) | ~m1_pre_topc(B_405, A_407) | v2_struct_0(B_405) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407) | v2_struct_0(A_407))), inference(cnfTransformation, [status(thm)], [f_160])).
% 16.20/7.87  tff(c_1615, plain, (![B_405, A_407]: (m1_pre_topc(B_405, '#skF_3') | k1_tsep_1(A_407, B_405, '#skF_3')!=g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', A_407) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_405, A_407) | v2_struct_0(B_405) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407) | v2_struct_0(A_407))), inference(superposition, [status(thm), theory('equality')], [c_131, c_1609])).
% 16.20/7.87  tff(c_1623, plain, (![B_405, A_407]: (m1_pre_topc(B_405, '#skF_3') | k1_tsep_1(A_407, B_405, '#skF_3')!='#skF_4' | ~m1_pre_topc('#skF_3', A_407) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_405, A_407) | v2_struct_0(B_405) | ~l1_pre_topc(A_407) | ~v2_pre_topc(A_407) | v2_struct_0(A_407))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_1615])).
% 16.20/7.87  tff(c_1648, plain, (![B_411, A_412]: (m1_pre_topc(B_411, '#skF_3') | k1_tsep_1(A_412, B_411, '#skF_3')!='#skF_4' | ~m1_pre_topc('#skF_3', A_412) | ~m1_pre_topc(B_411, A_412) | v2_struct_0(B_411) | ~l1_pre_topc(A_412) | ~v2_pre_topc(A_412) | v2_struct_0(A_412))), inference(negUnitSimplification, [status(thm)], [c_66, c_1623])).
% 16.20/7.87  tff(c_1657, plain, (![B_411]: (m1_pre_topc(B_411, '#skF_3') | k1_tsep_1('#skF_1', B_411, '#skF_3')!='#skF_4' | ~m1_pre_topc(B_411, '#skF_1') | v2_struct_0(B_411) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_1648])).
% 16.20/7.87  tff(c_1668, plain, (![B_411]: (m1_pre_topc(B_411, '#skF_3') | k1_tsep_1('#skF_1', B_411, '#skF_3')!='#skF_4' | ~m1_pre_topc(B_411, '#skF_1') | v2_struct_0(B_411) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1657])).
% 16.20/7.87  tff(c_1670, plain, (![B_413]: (m1_pre_topc(B_413, '#skF_3') | k1_tsep_1('#skF_1', B_413, '#skF_3')!='#skF_4' | ~m1_pre_topc(B_413, '#skF_1') | v2_struct_0(B_413))), inference(negUnitSimplification, [status(thm)], [c_78, c_1668])).
% 16.20/7.87  tff(c_189, plain, (![B_326]: (m1_subset_1(u1_struct_0(B_326), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_326, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_177])).
% 16.20/7.87  tff(c_223, plain, (![B_329]: (m1_subset_1(u1_struct_0(B_329), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_329, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_189])).
% 16.20/7.87  tff(c_229, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_223])).
% 16.20/7.87  tff(c_335, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_229])).
% 16.20/7.87  tff(c_1701, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')!='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1670, c_335])).
% 16.20/7.87  tff(c_1758, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1120, c_1701])).
% 16.20/7.87  tff(c_1760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1758])).
% 16.20/7.87  tff(c_1762, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_229])).
% 16.20/7.87  tff(c_2073, plain, (![A_430, B_431]: (k1_tsep_1(A_430, B_431, B_431)=g1_pre_topc(u1_struct_0(B_431), u1_pre_topc(B_431)) | ~m1_pre_topc(B_431, A_430) | v2_struct_0(B_431) | ~l1_pre_topc(A_430) | ~v2_pre_topc(A_430) | v2_struct_0(A_430))), inference(cnfTransformation, [status(thm)], [f_175])).
% 16.20/7.87  tff(c_2077, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_3', '#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1762, c_2073])).
% 16.20/7.87  tff(c_2090, plain, (k1_tsep_1('#skF_3', '#skF_3', '#skF_3')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_123, c_136, c_131, c_2077])).
% 16.20/7.87  tff(c_2091, plain, (k1_tsep_1('#skF_3', '#skF_3', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_66, c_2090])).
% 16.20/7.87  tff(c_2300, plain, (![B_441, A_442, C_443]: (m1_pre_topc(B_441, k1_tsep_1(A_442, B_441, C_443)) | ~m1_pre_topc(C_443, A_442) | v2_struct_0(C_443) | ~m1_pre_topc(B_441, A_442) | v2_struct_0(B_441) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.20/7.87  tff(c_2334, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2091, c_2300])).
% 16.20/7.87  tff(c_2356, plain, (m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_123, c_1762, c_1762, c_2334])).
% 16.20/7.87  tff(c_2358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1831, c_2356])).
% 16.20/7.87  tff(c_2360, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_216])).
% 16.20/7.87  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.87  tff(c_147, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_50])).
% 16.20/7.87  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.87  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.87  tff(c_79, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 16.20/7.87  tff(c_137, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_79])).
% 16.20/7.87  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_286])).
% 16.20/7.87  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 16.20/7.87  tff(c_3747, plain, (![G_502, A_497, C_498, B_499, D_501, E_500]: (r1_tmap_1(D_501, B_499, E_500, G_502) | ~r1_tmap_1(C_498, B_499, k3_tmap_1(A_497, B_499, D_501, C_498, E_500), G_502) | ~m1_subset_1(G_502, u1_struct_0(C_498)) | ~m1_subset_1(G_502, u1_struct_0(D_501)) | ~m1_pre_topc(C_498, D_501) | ~v1_tsep_1(C_498, D_501) | ~m1_subset_1(E_500, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_501), u1_struct_0(B_499)))) | ~v1_funct_2(E_500, u1_struct_0(D_501), u1_struct_0(B_499)) | ~v1_funct_1(E_500) | ~m1_pre_topc(D_501, A_497) | v2_struct_0(D_501) | ~m1_pre_topc(C_498, A_497) | v2_struct_0(C_498) | ~l1_pre_topc(B_499) | ~v2_pre_topc(B_499) | v2_struct_0(B_499) | ~l1_pre_topc(A_497) | ~v2_pre_topc(A_497) | v2_struct_0(A_497))), inference(cnfTransformation, [status(thm)], [f_237])).
% 16.20/7.87  tff(c_3749, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_3747])).
% 16.20/7.87  tff(c_3752, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_146, c_103, c_135, c_152, c_103, c_135, c_2360, c_147, c_135, c_137, c_131, c_3749])).
% 16.20/7.87  tff(c_3753, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_42, c_3752])).
% 16.20/7.87  tff(c_2359, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_216])).
% 16.20/7.87  tff(c_159, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_153])).
% 16.20/7.87  tff(c_165, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_159])).
% 16.20/7.87  tff(c_2602, plain, (![B_452, A_453]: (v1_tsep_1(B_452, A_453) | ~v3_pre_topc(u1_struct_0(B_452), A_453) | ~m1_subset_1(u1_struct_0(B_452), k1_zfmisc_1(u1_struct_0(A_453))) | ~m1_pre_topc(B_452, A_453) | ~l1_pre_topc(A_453) | ~v2_pre_topc(A_453))), inference(cnfTransformation, [status(thm)], [f_109])).
% 16.20/7.87  tff(c_2611, plain, (![B_452]: (v1_tsep_1(B_452, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_452), '#skF_4') | ~m1_subset_1(u1_struct_0(B_452), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_452, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_2602])).
% 16.20/7.87  tff(c_31147, plain, (![B_943]: (v1_tsep_1(B_943, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_943), '#skF_4') | ~m1_subset_1(u1_struct_0(B_943), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_943, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_126, c_2611])).
% 16.20/7.87  tff(c_31171, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_131, c_31147])).
% 16.20/7.87  tff(c_31186, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_2359, c_131, c_31171])).
% 16.20/7.87  tff(c_31187, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3753, c_31186])).
% 16.20/7.87  tff(c_1761, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_229])).
% 16.20/7.87  tff(c_12, plain, (![A_16]: (v3_pre_topc(k2_struct_0(A_16), A_16) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.20/7.87  tff(c_26, plain, (![B_44, A_42]: (m1_subset_1(u1_struct_0(B_44), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_pre_topc(B_44, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.20/7.87  tff(c_3217, plain, (![B_477, A_478]: (v1_tsep_1(B_477, A_478) | ~v3_pre_topc(u1_struct_0(B_477), A_478) | ~v2_pre_topc(A_478) | ~m1_pre_topc(B_477, A_478) | ~l1_pre_topc(A_478))), inference(resolution, [status(thm)], [c_26, c_2602])).
% 16.20/7.87  tff(c_3672, plain, (![A_492]: (v1_tsep_1('#skF_3', A_492) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_492) | ~v2_pre_topc(A_492) | ~m1_pre_topc('#skF_3', A_492) | ~l1_pre_topc(A_492))), inference(superposition, [status(thm), theory('equality')], [c_131, c_3217])).
% 16.20/7.87  tff(c_3676, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_3672])).
% 16.20/7.87  tff(c_3679, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_123, c_1762, c_3676])).
% 16.20/7.87  tff(c_2413, plain, (![B_444, A_445]: (v3_pre_topc(u1_struct_0(B_444), A_445) | ~v1_tsep_1(B_444, A_445) | ~m1_subset_1(u1_struct_0(B_444), k1_zfmisc_1(u1_struct_0(A_445))) | ~m1_pre_topc(B_444, A_445) | ~l1_pre_topc(A_445) | ~v2_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_109])).
% 16.20/7.87  tff(c_2428, plain, (![B_444]: (v3_pre_topc(u1_struct_0(B_444), '#skF_3') | ~v1_tsep_1(B_444, '#skF_3') | ~m1_subset_1(u1_struct_0(B_444), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_444, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_2413])).
% 16.20/7.87  tff(c_31406, plain, (![B_947]: (v3_pre_topc(u1_struct_0(B_947), '#skF_3') | ~v1_tsep_1(B_947, '#skF_3') | ~m1_subset_1(u1_struct_0(B_947), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_947, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_123, c_2428])).
% 16.20/7.87  tff(c_31433, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_31406])).
% 16.20/7.87  tff(c_31449, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1762, c_1761, c_3679, c_131, c_31433])).
% 16.20/7.87  tff(c_236, plain, (![B_330, A_331]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_330), u1_pre_topc(B_330)), A_331) | ~m1_pre_topc(B_330, A_331) | ~l1_pre_topc(A_331))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.20/7.87  tff(c_250, plain, (![A_331]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_331) | ~m1_pre_topc('#skF_3', A_331) | ~l1_pre_topc(A_331))), inference(superposition, [status(thm), theory('equality')], [c_131, c_236])).
% 16.20/7.87  tff(c_260, plain, (![A_331]: (m1_pre_topc('#skF_4', A_331) | ~m1_pre_topc('#skF_3', A_331) | ~l1_pre_topc(A_331))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_250])).
% 16.20/7.87  tff(c_1767, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1762, c_260])).
% 16.20/7.87  tff(c_1779, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_1767])).
% 16.20/7.87  tff(c_2867, plain, (![D_462, C_463, A_464]: (v3_pre_topc(D_462, C_463) | ~m1_subset_1(D_462, k1_zfmisc_1(u1_struct_0(C_463))) | ~v3_pre_topc(D_462, A_464) | ~m1_pre_topc(C_463, A_464) | ~m1_subset_1(D_462, k1_zfmisc_1(u1_struct_0(A_464))) | ~l1_pre_topc(A_464))), inference(cnfTransformation, [status(thm)], [f_82])).
% 16.20/7.87  tff(c_4862, plain, (![B_538, A_539, A_540]: (v3_pre_topc(u1_struct_0(B_538), A_539) | ~v3_pre_topc(u1_struct_0(B_538), A_540) | ~m1_pre_topc(A_539, A_540) | ~m1_subset_1(u1_struct_0(B_538), k1_zfmisc_1(u1_struct_0(A_540))) | ~l1_pre_topc(A_540) | ~m1_pre_topc(B_538, A_539) | ~l1_pre_topc(A_539))), inference(resolution, [status(thm)], [c_26, c_2867])).
% 16.20/7.87  tff(c_4888, plain, (![B_538]: (v3_pre_topc(u1_struct_0(B_538), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_538), '#skF_3') | ~m1_subset_1(u1_struct_0(B_538), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_538, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1779, c_4862])).
% 16.20/7.87  tff(c_35884, plain, (![B_1015]: (v3_pre_topc(u1_struct_0(B_1015), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_1015), '#skF_3') | ~m1_subset_1(u1_struct_0(B_1015), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_1015, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_123, c_131, c_4888])).
% 16.20/7.87  tff(c_35911, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_131, c_35884])).
% 16.20/7.87  tff(c_35927, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2360, c_1761, c_31449, c_131, c_131, c_35911])).
% 16.20/7.87  tff(c_35929, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31187, c_35927])).
% 16.20/7.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.20/7.87  
% 16.20/7.87  Inference rules
% 16.20/7.87  ----------------------
% 16.20/7.87  #Ref     : 0
% 16.20/7.87  #Sup     : 8585
% 16.20/7.87  #Fact    : 0
% 16.20/7.87  #Define  : 0
% 16.20/7.87  #Split   : 54
% 16.20/7.87  #Chain   : 0
% 16.20/7.87  #Close   : 0
% 16.20/7.87  
% 16.20/7.87  Ordering : KBO
% 16.20/7.87  
% 16.20/7.87  Simplification rules
% 16.20/7.87  ----------------------
% 16.20/7.87  #Subsume      : 1892
% 16.20/7.87  #Demod        : 14388
% 16.20/7.87  #Tautology    : 2071
% 16.20/7.87  #SimpNegUnit  : 844
% 16.20/7.87  #BackRed      : 22
% 16.20/7.87  
% 16.20/7.87  #Partial instantiations: 0
% 16.20/7.87  #Strategies tried      : 1
% 16.20/7.87  
% 16.20/7.87  Timing (in seconds)
% 16.20/7.87  ----------------------
% 16.20/7.87  Preprocessing        : 0.40
% 16.20/7.87  Parsing              : 0.20
% 16.20/7.87  CNF conversion       : 0.05
% 16.20/7.87  Main loop            : 6.67
% 16.20/7.87  Inferencing          : 1.24
% 16.20/7.87  Reduction            : 2.85
% 16.20/7.87  Demodulation         : 2.31
% 16.20/7.87  BG Simplification    : 0.16
% 16.20/7.87  Subsumption          : 2.13
% 16.20/7.87  Abstraction          : 0.23
% 16.20/7.87  MUC search           : 0.00
% 16.20/7.87  Cooper               : 0.00
% 16.20/7.87  Total                : 7.12
% 16.20/7.87  Index Insertion      : 0.00
% 16.20/7.87  Index Deletion       : 0.00
% 16.20/7.87  Index Matching       : 0.00
% 16.20/7.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
