%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:32 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  159 (1438 expanded)
%              Number of leaves         :   45 ( 511 expanded)
%              Depth                    :   19
%              Number of atoms          :  372 (6690 expanded)
%              Number of equality atoms :   42 ( 753 expanded)
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

tff(f_250,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_201,axiom,(
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

tff(f_96,axiom,(
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

tff(c_82,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_46,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_80,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_78,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_68,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_120,plain,(
    ! [B_306,A_307] :
      ( l1_pre_topc(B_306)
      | ~ m1_pre_topc(B_306,A_307)
      | ~ l1_pre_topc(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_129,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_120])).

tff(c_136,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_129])).

tff(c_14,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_93,plain,(
    ! [A_304] :
      ( u1_struct_0(A_304) = k2_struct_0(A_304)
      | ~ l1_struct_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_144,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_97])).

tff(c_102,plain,(
    ! [A_305] :
      ( u1_struct_0(A_305) = k2_struct_0(A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_109,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_102])).

tff(c_60,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_111,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_60])).

tff(c_153,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_111])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_151,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_58])).

tff(c_152,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_151])).

tff(c_126,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_133,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_126])).

tff(c_140,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_171,plain,(
    ! [B_311,A_312] :
      ( v2_pre_topc(B_311)
      | ~ m1_pre_topc(B_311,A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_180,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_187,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_180])).

tff(c_34,plain,(
    ! [A_39] :
      ( m1_pre_topc(A_39,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_307,plain,(
    ! [B_317,A_318] :
      ( m1_subset_1(u1_struct_0(B_317),k1_zfmisc_1(u1_struct_0(A_318)))
      | ~ m1_pre_topc(B_317,A_318)
      | ~ l1_pre_topc(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_313,plain,(
    ! [B_317] :
      ( m1_subset_1(u1_struct_0(B_317),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_317,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_307])).

tff(c_340,plain,(
    ! [B_319] :
      ( m1_subset_1(u1_struct_0(B_319),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_319,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_313])).

tff(c_343,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_340])).

tff(c_415,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_418,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_415])).

tff(c_422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_418])).

tff(c_424,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_3728,plain,(
    ! [B_562,C_563,A_564] :
      ( r1_tarski(u1_struct_0(B_562),u1_struct_0(C_563))
      | ~ m1_pre_topc(B_562,C_563)
      | ~ m1_pre_topc(C_563,A_564)
      | ~ m1_pre_topc(B_562,A_564)
      | ~ l1_pre_topc(A_564)
      | ~ v2_pre_topc(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3734,plain,(
    ! [B_562] :
      ( r1_tarski(u1_struct_0(B_562),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_562,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_424,c_3728])).

tff(c_3756,plain,(
    ! [B_565] :
      ( r1_tarski(u1_struct_0(B_565),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_565,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_136,c_144,c_3734])).

tff(c_3764,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_3756])).

tff(c_3774,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3764])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_145,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_56])).

tff(c_188,plain,(
    ! [A_313] :
      ( g1_pre_topc(u1_struct_0(A_313),u1_pre_topc(A_313)) = A_313
      | ~ v1_pre_topc(A_313)
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_188])).

tff(c_210,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_197])).

tff(c_248,plain,(
    ~ v1_pre_topc('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_249,plain,(
    ! [A_315] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_315),u1_pre_topc(A_315)))
      | ~ l1_pre_topc(A_315)
      | v2_struct_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_258,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_249])).

tff(c_269,plain,
    ( v1_pre_topc('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_145,c_258])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_248,c_269])).

tff(c_272,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_3969,plain,(
    ! [D_571,B_572,C_573,A_574] :
      ( m1_pre_topc(D_571,B_572)
      | ~ m1_pre_topc(C_573,A_574)
      | g1_pre_topc(u1_struct_0(D_571),u1_pre_topc(D_571)) != g1_pre_topc(u1_struct_0(C_573),u1_pre_topc(C_573))
      | g1_pre_topc(u1_struct_0(B_572),u1_pre_topc(B_572)) != g1_pre_topc(u1_struct_0(A_574),u1_pre_topc(A_574))
      | ~ l1_pre_topc(D_571)
      | ~ l1_pre_topc(C_573)
      | ~ l1_pre_topc(B_572)
      | ~ l1_pre_topc(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4001,plain,(
    ! [D_571,B_572,A_39] :
      ( m1_pre_topc(D_571,B_572)
      | g1_pre_topc(u1_struct_0(D_571),u1_pre_topc(D_571)) != g1_pre_topc(u1_struct_0(A_39),u1_pre_topc(A_39))
      | g1_pre_topc(u1_struct_0(B_572),u1_pre_topc(B_572)) != g1_pre_topc(u1_struct_0(A_39),u1_pre_topc(A_39))
      | ~ l1_pre_topc(D_571)
      | ~ l1_pre_topc(B_572)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_34,c_3969])).

tff(c_5211,plain,(
    ! [A_672,B_673] :
      ( m1_pre_topc(A_672,B_673)
      | g1_pre_topc(u1_struct_0(B_673),u1_pre_topc(B_673)) != g1_pre_topc(u1_struct_0(A_672),u1_pre_topc(A_672))
      | ~ l1_pre_topc(A_672)
      | ~ l1_pre_topc(B_673)
      | ~ l1_pre_topc(A_672) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4001])).

tff(c_5217,plain,(
    ! [A_672] :
      ( m1_pre_topc(A_672,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_672),u1_pre_topc(A_672)) != g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(A_672)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_672) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_5211])).

tff(c_5248,plain,(
    ! [A_674] :
      ( m1_pre_topc(A_674,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_674),u1_pre_topc(A_674)) != '#skF_4'
      | ~ l1_pre_topc(A_674) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_272,c_5217])).

tff(c_5257,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_5248])).

tff(c_5267,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_145,c_5257])).

tff(c_5269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3774,c_5267])).

tff(c_5271,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3764])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_154,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_54])).

tff(c_5270,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3764])).

tff(c_319,plain,(
    ! [B_317] :
      ( m1_subset_1(u1_struct_0(B_317),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_317,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_307])).

tff(c_366,plain,(
    ! [B_321] :
      ( m1_subset_1(u1_struct_0(B_321),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_321,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_319])).

tff(c_369,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_366])).

tff(c_477,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_2319,plain,(
    ! [D_451,B_452,C_453,A_454] :
      ( m1_pre_topc(D_451,B_452)
      | ~ m1_pre_topc(C_453,A_454)
      | g1_pre_topc(u1_struct_0(D_451),u1_pre_topc(D_451)) != g1_pre_topc(u1_struct_0(C_453),u1_pre_topc(C_453))
      | g1_pre_topc(u1_struct_0(B_452),u1_pre_topc(B_452)) != g1_pre_topc(u1_struct_0(A_454),u1_pre_topc(A_454))
      | ~ l1_pre_topc(D_451)
      | ~ l1_pre_topc(C_453)
      | ~ l1_pre_topc(B_452)
      | ~ l1_pre_topc(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2356,plain,(
    ! [D_451,B_452,A_39] :
      ( m1_pre_topc(D_451,B_452)
      | g1_pre_topc(u1_struct_0(D_451),u1_pre_topc(D_451)) != g1_pre_topc(u1_struct_0(A_39),u1_pre_topc(A_39))
      | g1_pre_topc(u1_struct_0(B_452),u1_pre_topc(B_452)) != g1_pre_topc(u1_struct_0(A_39),u1_pre_topc(A_39))
      | ~ l1_pre_topc(D_451)
      | ~ l1_pre_topc(B_452)
      | ~ l1_pre_topc(A_39) ) ),
    inference(resolution,[status(thm)],[c_34,c_2319])).

tff(c_3580,plain,(
    ! [A_552,B_553] :
      ( m1_pre_topc(A_552,B_553)
      | g1_pre_topc(u1_struct_0(B_553),u1_pre_topc(B_553)) != g1_pre_topc(u1_struct_0(A_552),u1_pre_topc(A_552))
      | ~ l1_pre_topc(A_552)
      | ~ l1_pre_topc(B_553)
      | ~ l1_pre_topc(A_552) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2356])).

tff(c_3590,plain,(
    ! [A_552] :
      ( m1_pre_topc(A_552,'#skF_3')
      | g1_pre_topc(u1_struct_0(A_552),u1_pre_topc(A_552)) != g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(A_552)
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_552) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_3580])).

tff(c_3691,plain,(
    ! [A_561] :
      ( m1_pre_topc(A_561,'#skF_3')
      | g1_pre_topc(u1_struct_0(A_561),u1_pre_topc(A_561)) != '#skF_4'
      | ~ l1_pre_topc(A_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_145,c_3590])).

tff(c_3697,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != '#skF_4'
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_3691])).

tff(c_3708,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_272,c_3697])).

tff(c_3710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_3708])).

tff(c_3712,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_177,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_171])).

tff(c_184,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_177])).

tff(c_372,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_366])).

tff(c_5297,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_5303,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_5297])).

tff(c_5310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_5303])).

tff(c_5312,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_372])).

tff(c_36,plain,(
    ! [B_44,C_46,A_40] :
      ( r1_tarski(u1_struct_0(B_44),u1_struct_0(C_46))
      | ~ m1_pre_topc(B_44,C_46)
      | ~ m1_pre_topc(C_46,A_40)
      | ~ m1_pre_topc(B_44,A_40)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5355,plain,(
    ! [B_44] :
      ( r1_tarski(u1_struct_0(B_44),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_44,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5312,c_36])).

tff(c_5374,plain,(
    ! [B_677] :
      ( r1_tarski(u1_struct_0(B_677),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_677,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_133,c_140,c_5355])).

tff(c_5379,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_5374])).

tff(c_5391,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3712,c_5379])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5396,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5391,c_2])).

tff(c_5399,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5270,c_5396])).

tff(c_5409,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5399,c_140])).

tff(c_50,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_48,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_84,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_5951,plain,(
    ! [B_712,E_708,C_711,A_710,D_707,G_709] :
      ( r1_tmap_1(D_707,B_712,E_708,G_709)
      | ~ r1_tmap_1(C_711,B_712,k3_tmap_1(A_710,B_712,D_707,C_711,E_708),G_709)
      | ~ m1_subset_1(G_709,u1_struct_0(C_711))
      | ~ m1_subset_1(G_709,u1_struct_0(D_707))
      | ~ m1_pre_topc(C_711,D_707)
      | ~ v1_tsep_1(C_711,D_707)
      | ~ m1_subset_1(E_708,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_707),u1_struct_0(B_712))))
      | ~ v1_funct_2(E_708,u1_struct_0(D_707),u1_struct_0(B_712))
      | ~ v1_funct_1(E_708)
      | ~ m1_pre_topc(D_707,A_710)
      | v2_struct_0(D_707)
      | ~ m1_pre_topc(C_711,A_710)
      | v2_struct_0(C_711)
      | ~ l1_pre_topc(B_712)
      | ~ v2_pre_topc(B_712)
      | v2_struct_0(B_712)
      | ~ l1_pre_topc(A_710)
      | ~ v2_pre_topc(A_710)
      | v2_struct_0(A_710) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_5953,plain,
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
    inference(resolution,[status(thm)],[c_84,c_5951])).

tff(c_5956,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_72,c_68,c_64,c_62,c_153,c_109,c_144,c_152,c_109,c_144,c_5271,c_154,c_144,c_154,c_5409,c_5953])).

tff(c_5957,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_70,c_66,c_46,c_5956])).

tff(c_24,plain,(
    ! [A_28] :
      ( v3_pre_topc(k2_struct_0(A_28),A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    ! [B_38,A_36] :
      ( m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5485,plain,(
    ! [B_678,A_679] :
      ( v1_tsep_1(B_678,A_679)
      | ~ v3_pre_topc(u1_struct_0(B_678),A_679)
      | ~ m1_subset_1(u1_struct_0(B_678),k1_zfmisc_1(u1_struct_0(A_679)))
      | ~ m1_pre_topc(B_678,A_679)
      | ~ l1_pre_topc(A_679)
      | ~ v2_pre_topc(A_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6260,plain,(
    ! [B_734,A_735] :
      ( v1_tsep_1(B_734,A_735)
      | ~ v3_pre_topc(u1_struct_0(B_734),A_735)
      | ~ v2_pre_topc(A_735)
      | ~ m1_pre_topc(B_734,A_735)
      | ~ l1_pre_topc(A_735) ) ),
    inference(resolution,[status(thm)],[c_32,c_5485])).

tff(c_6553,plain,(
    ! [A_762] :
      ( v1_tsep_1('#skF_3',A_762)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_762)
      | ~ v2_pre_topc(A_762)
      | ~ m1_pre_topc('#skF_3',A_762)
      | ~ l1_pre_topc(A_762) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5409,c_6260])).

tff(c_6566,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_6553])).

tff(c_6574,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_136,c_5271,c_6566])).

tff(c_6576,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5957,c_6574])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.38/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.72  
% 7.45/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.45/2.73  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.45/2.73  
% 7.45/2.73  %Foreground sorts:
% 7.45/2.73  
% 7.45/2.73  
% 7.45/2.73  %Background operators:
% 7.45/2.73  
% 7.45/2.73  
% 7.45/2.73  %Foreground operators:
% 7.45/2.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.45/2.73  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.45/2.73  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.45/2.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.45/2.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.45/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.45/2.73  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.45/2.73  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.45/2.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.45/2.73  tff('#skF_7', type, '#skF_7': $i).
% 7.45/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.45/2.73  tff('#skF_5', type, '#skF_5': $i).
% 7.45/2.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.45/2.73  tff('#skF_6', type, '#skF_6': $i).
% 7.45/2.73  tff('#skF_2', type, '#skF_2': $i).
% 7.45/2.73  tff('#skF_3', type, '#skF_3': $i).
% 7.45/2.73  tff('#skF_1', type, '#skF_1': $i).
% 7.45/2.73  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.45/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.45/2.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.45/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.45/2.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.45/2.73  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 7.45/2.73  tff('#skF_4', type, '#skF_4': $i).
% 7.45/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.45/2.73  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.45/2.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.45/2.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.45/2.73  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.45/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.45/2.73  
% 7.49/2.75  tff(f_250, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 7.49/2.75  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.49/2.75  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.49/2.75  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.49/2.75  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.49/2.75  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.49/2.75  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.49/2.75  tff(f_139, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 7.49/2.75  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 7.49/2.75  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_pre_topc)).
% 7.49/2.75  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_pre_topc)).
% 7.49/2.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.49/2.75  tff(f_201, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 7.49/2.75  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 7.49/2.75  tff(f_114, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 7.49/2.75  tff(c_82, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_46, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_80, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_78, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_68, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_120, plain, (![B_306, A_307]: (l1_pre_topc(B_306) | ~m1_pre_topc(B_306, A_307) | ~l1_pre_topc(A_307))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.49/2.75  tff(c_129, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_120])).
% 7.49/2.75  tff(c_136, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_129])).
% 7.49/2.75  tff(c_14, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.49/2.75  tff(c_93, plain, (![A_304]: (u1_struct_0(A_304)=k2_struct_0(A_304) | ~l1_struct_0(A_304))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.49/2.75  tff(c_97, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_14, c_93])).
% 7.49/2.75  tff(c_144, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_136, c_97])).
% 7.49/2.75  tff(c_102, plain, (![A_305]: (u1_struct_0(A_305)=k2_struct_0(A_305) | ~l1_pre_topc(A_305))), inference(resolution, [status(thm)], [c_14, c_93])).
% 7.49/2.75  tff(c_109, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_72, c_102])).
% 7.49/2.75  tff(c_60, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_111, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_60])).
% 7.49/2.75  tff(c_153, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_111])).
% 7.49/2.75  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_151, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_58])).
% 7.49/2.75  tff(c_152, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_151])).
% 7.49/2.75  tff(c_126, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_120])).
% 7.49/2.75  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_126])).
% 7.49/2.75  tff(c_140, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_97])).
% 7.49/2.75  tff(c_171, plain, (![B_311, A_312]: (v2_pre_topc(B_311) | ~m1_pre_topc(B_311, A_312) | ~l1_pre_topc(A_312) | ~v2_pre_topc(A_312))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.49/2.75  tff(c_180, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_171])).
% 7.49/2.75  tff(c_187, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_180])).
% 7.49/2.75  tff(c_34, plain, (![A_39]: (m1_pre_topc(A_39, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.49/2.75  tff(c_307, plain, (![B_317, A_318]: (m1_subset_1(u1_struct_0(B_317), k1_zfmisc_1(u1_struct_0(A_318))) | ~m1_pre_topc(B_317, A_318) | ~l1_pre_topc(A_318))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.49/2.75  tff(c_313, plain, (![B_317]: (m1_subset_1(u1_struct_0(B_317), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_317, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_307])).
% 7.49/2.75  tff(c_340, plain, (![B_319]: (m1_subset_1(u1_struct_0(B_319), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_319, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_313])).
% 7.49/2.75  tff(c_343, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_144, c_340])).
% 7.49/2.75  tff(c_415, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_343])).
% 7.49/2.75  tff(c_418, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_415])).
% 7.49/2.75  tff(c_422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_418])).
% 7.49/2.75  tff(c_424, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_343])).
% 7.49/2.75  tff(c_3728, plain, (![B_562, C_563, A_564]: (r1_tarski(u1_struct_0(B_562), u1_struct_0(C_563)) | ~m1_pre_topc(B_562, C_563) | ~m1_pre_topc(C_563, A_564) | ~m1_pre_topc(B_562, A_564) | ~l1_pre_topc(A_564) | ~v2_pre_topc(A_564))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.49/2.75  tff(c_3734, plain, (![B_562]: (r1_tarski(u1_struct_0(B_562), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_562, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_424, c_3728])).
% 7.49/2.75  tff(c_3756, plain, (![B_565]: (r1_tarski(u1_struct_0(B_565), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_565, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_136, c_144, c_3734])).
% 7.49/2.75  tff(c_3764, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_140, c_3756])).
% 7.49/2.75  tff(c_3774, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_3764])).
% 7.49/2.75  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_145, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_56])).
% 7.49/2.75  tff(c_188, plain, (![A_313]: (g1_pre_topc(u1_struct_0(A_313), u1_pre_topc(A_313))=A_313 | ~v1_pre_topc(A_313) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.49/2.75  tff(c_197, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_144, c_188])).
% 7.49/2.75  tff(c_210, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_197])).
% 7.49/2.75  tff(c_248, plain, (~v1_pre_topc('#skF_4')), inference(splitLeft, [status(thm)], [c_210])).
% 7.49/2.75  tff(c_249, plain, (![A_315]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_315), u1_pre_topc(A_315))) | ~l1_pre_topc(A_315) | v2_struct_0(A_315))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.49/2.75  tff(c_258, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_249])).
% 7.49/2.75  tff(c_269, plain, (v1_pre_topc('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_145, c_258])).
% 7.49/2.75  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_248, c_269])).
% 7.49/2.75  tff(c_272, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_210])).
% 7.49/2.75  tff(c_3969, plain, (![D_571, B_572, C_573, A_574]: (m1_pre_topc(D_571, B_572) | ~m1_pre_topc(C_573, A_574) | g1_pre_topc(u1_struct_0(D_571), u1_pre_topc(D_571))!=g1_pre_topc(u1_struct_0(C_573), u1_pre_topc(C_573)) | g1_pre_topc(u1_struct_0(B_572), u1_pre_topc(B_572))!=g1_pre_topc(u1_struct_0(A_574), u1_pre_topc(A_574)) | ~l1_pre_topc(D_571) | ~l1_pre_topc(C_573) | ~l1_pre_topc(B_572) | ~l1_pre_topc(A_574))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.49/2.75  tff(c_4001, plain, (![D_571, B_572, A_39]: (m1_pre_topc(D_571, B_572) | g1_pre_topc(u1_struct_0(D_571), u1_pre_topc(D_571))!=g1_pre_topc(u1_struct_0(A_39), u1_pre_topc(A_39)) | g1_pre_topc(u1_struct_0(B_572), u1_pre_topc(B_572))!=g1_pre_topc(u1_struct_0(A_39), u1_pre_topc(A_39)) | ~l1_pre_topc(D_571) | ~l1_pre_topc(B_572) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_34, c_3969])).
% 7.49/2.75  tff(c_5211, plain, (![A_672, B_673]: (m1_pre_topc(A_672, B_673) | g1_pre_topc(u1_struct_0(B_673), u1_pre_topc(B_673))!=g1_pre_topc(u1_struct_0(A_672), u1_pre_topc(A_672)) | ~l1_pre_topc(A_672) | ~l1_pre_topc(B_673) | ~l1_pre_topc(A_672))), inference(reflexivity, [status(thm), theory('equality')], [c_4001])).
% 7.49/2.75  tff(c_5217, plain, (![A_672]: (m1_pre_topc(A_672, '#skF_4') | g1_pre_topc(u1_struct_0(A_672), u1_pre_topc(A_672))!=g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc(A_672) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_672))), inference(superposition, [status(thm), theory('equality')], [c_144, c_5211])).
% 7.49/2.75  tff(c_5248, plain, (![A_674]: (m1_pre_topc(A_674, '#skF_4') | g1_pre_topc(u1_struct_0(A_674), u1_pre_topc(A_674))!='#skF_4' | ~l1_pre_topc(A_674))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_272, c_5217])).
% 7.49/2.75  tff(c_5257, plain, (m1_pre_topc('#skF_3', '#skF_4') | g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_4' | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_5248])).
% 7.49/2.75  tff(c_5267, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_145, c_5257])).
% 7.49/2.75  tff(c_5269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3774, c_5267])).
% 7.49/2.75  tff(c_5271, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_3764])).
% 7.49/2.75  tff(c_54, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_154, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_54])).
% 7.49/2.75  tff(c_5270, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_3764])).
% 7.49/2.75  tff(c_319, plain, (![B_317]: (m1_subset_1(u1_struct_0(B_317), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_317, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_307])).
% 7.49/2.75  tff(c_366, plain, (![B_321]: (m1_subset_1(u1_struct_0(B_321), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_321, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_319])).
% 7.49/2.75  tff(c_369, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_366])).
% 7.49/2.75  tff(c_477, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_369])).
% 7.49/2.75  tff(c_2319, plain, (![D_451, B_452, C_453, A_454]: (m1_pre_topc(D_451, B_452) | ~m1_pre_topc(C_453, A_454) | g1_pre_topc(u1_struct_0(D_451), u1_pre_topc(D_451))!=g1_pre_topc(u1_struct_0(C_453), u1_pre_topc(C_453)) | g1_pre_topc(u1_struct_0(B_452), u1_pre_topc(B_452))!=g1_pre_topc(u1_struct_0(A_454), u1_pre_topc(A_454)) | ~l1_pre_topc(D_451) | ~l1_pre_topc(C_453) | ~l1_pre_topc(B_452) | ~l1_pre_topc(A_454))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.49/2.75  tff(c_2356, plain, (![D_451, B_452, A_39]: (m1_pre_topc(D_451, B_452) | g1_pre_topc(u1_struct_0(D_451), u1_pre_topc(D_451))!=g1_pre_topc(u1_struct_0(A_39), u1_pre_topc(A_39)) | g1_pre_topc(u1_struct_0(B_452), u1_pre_topc(B_452))!=g1_pre_topc(u1_struct_0(A_39), u1_pre_topc(A_39)) | ~l1_pre_topc(D_451) | ~l1_pre_topc(B_452) | ~l1_pre_topc(A_39))), inference(resolution, [status(thm)], [c_34, c_2319])).
% 7.49/2.75  tff(c_3580, plain, (![A_552, B_553]: (m1_pre_topc(A_552, B_553) | g1_pre_topc(u1_struct_0(B_553), u1_pre_topc(B_553))!=g1_pre_topc(u1_struct_0(A_552), u1_pre_topc(A_552)) | ~l1_pre_topc(A_552) | ~l1_pre_topc(B_553) | ~l1_pre_topc(A_552))), inference(reflexivity, [status(thm), theory('equality')], [c_2356])).
% 7.49/2.75  tff(c_3590, plain, (![A_552]: (m1_pre_topc(A_552, '#skF_3') | g1_pre_topc(u1_struct_0(A_552), u1_pre_topc(A_552))!=g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~l1_pre_topc(A_552) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_552))), inference(superposition, [status(thm), theory('equality')], [c_140, c_3580])).
% 7.49/2.75  tff(c_3691, plain, (![A_561]: (m1_pre_topc(A_561, '#skF_3') | g1_pre_topc(u1_struct_0(A_561), u1_pre_topc(A_561))!='#skF_4' | ~l1_pre_topc(A_561))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_145, c_3590])).
% 7.49/2.75  tff(c_3697, plain, (m1_pre_topc('#skF_4', '#skF_3') | g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!='#skF_4' | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_144, c_3691])).
% 7.49/2.75  tff(c_3708, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_272, c_3697])).
% 7.49/2.75  tff(c_3710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_3708])).
% 7.49/2.75  tff(c_3712, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_369])).
% 7.49/2.75  tff(c_177, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_171])).
% 7.49/2.75  tff(c_184, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_177])).
% 7.49/2.75  tff(c_372, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_366])).
% 7.49/2.75  tff(c_5297, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_372])).
% 7.49/2.75  tff(c_5303, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_5297])).
% 7.49/2.75  tff(c_5310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_5303])).
% 7.49/2.75  tff(c_5312, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_372])).
% 7.49/2.75  tff(c_36, plain, (![B_44, C_46, A_40]: (r1_tarski(u1_struct_0(B_44), u1_struct_0(C_46)) | ~m1_pre_topc(B_44, C_46) | ~m1_pre_topc(C_46, A_40) | ~m1_pre_topc(B_44, A_40) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.49/2.75  tff(c_5355, plain, (![B_44]: (r1_tarski(u1_struct_0(B_44), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_44, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_5312, c_36])).
% 7.49/2.75  tff(c_5374, plain, (![B_677]: (r1_tarski(u1_struct_0(B_677), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_677, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_133, c_140, c_5355])).
% 7.49/2.75  tff(c_5379, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_5374])).
% 7.49/2.75  tff(c_5391, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3712, c_5379])).
% 7.49/2.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.49/2.75  tff(c_5396, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_5391, c_2])).
% 7.49/2.75  tff(c_5399, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5270, c_5396])).
% 7.49/2.75  tff(c_5409, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5399, c_140])).
% 7.49/2.75  tff(c_50, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_48, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_250])).
% 7.49/2.75  tff(c_84, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 7.49/2.75  tff(c_5951, plain, (![B_712, E_708, C_711, A_710, D_707, G_709]: (r1_tmap_1(D_707, B_712, E_708, G_709) | ~r1_tmap_1(C_711, B_712, k3_tmap_1(A_710, B_712, D_707, C_711, E_708), G_709) | ~m1_subset_1(G_709, u1_struct_0(C_711)) | ~m1_subset_1(G_709, u1_struct_0(D_707)) | ~m1_pre_topc(C_711, D_707) | ~v1_tsep_1(C_711, D_707) | ~m1_subset_1(E_708, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_707), u1_struct_0(B_712)))) | ~v1_funct_2(E_708, u1_struct_0(D_707), u1_struct_0(B_712)) | ~v1_funct_1(E_708) | ~m1_pre_topc(D_707, A_710) | v2_struct_0(D_707) | ~m1_pre_topc(C_711, A_710) | v2_struct_0(C_711) | ~l1_pre_topc(B_712) | ~v2_pre_topc(B_712) | v2_struct_0(B_712) | ~l1_pre_topc(A_710) | ~v2_pre_topc(A_710) | v2_struct_0(A_710))), inference(cnfTransformation, [status(thm)], [f_201])).
% 7.49/2.75  tff(c_5953, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_5951])).
% 7.49/2.75  tff(c_5956, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_72, c_68, c_64, c_62, c_153, c_109, c_144, c_152, c_109, c_144, c_5271, c_154, c_144, c_154, c_5409, c_5953])).
% 7.49/2.75  tff(c_5957, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_70, c_66, c_46, c_5956])).
% 7.49/2.75  tff(c_24, plain, (![A_28]: (v3_pre_topc(k2_struct_0(A_28), A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.49/2.75  tff(c_32, plain, (![B_38, A_36]: (m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.49/2.75  tff(c_5485, plain, (![B_678, A_679]: (v1_tsep_1(B_678, A_679) | ~v3_pre_topc(u1_struct_0(B_678), A_679) | ~m1_subset_1(u1_struct_0(B_678), k1_zfmisc_1(u1_struct_0(A_679))) | ~m1_pre_topc(B_678, A_679) | ~l1_pre_topc(A_679) | ~v2_pre_topc(A_679))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.49/2.75  tff(c_6260, plain, (![B_734, A_735]: (v1_tsep_1(B_734, A_735) | ~v3_pre_topc(u1_struct_0(B_734), A_735) | ~v2_pre_topc(A_735) | ~m1_pre_topc(B_734, A_735) | ~l1_pre_topc(A_735))), inference(resolution, [status(thm)], [c_32, c_5485])).
% 7.49/2.75  tff(c_6553, plain, (![A_762]: (v1_tsep_1('#skF_3', A_762) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_762) | ~v2_pre_topc(A_762) | ~m1_pre_topc('#skF_3', A_762) | ~l1_pre_topc(A_762))), inference(superposition, [status(thm), theory('equality')], [c_5409, c_6260])).
% 7.49/2.75  tff(c_6566, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_6553])).
% 7.49/2.75  tff(c_6574, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_136, c_5271, c_6566])).
% 7.49/2.75  tff(c_6576, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5957, c_6574])).
% 7.49/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.75  
% 7.49/2.75  Inference rules
% 7.49/2.75  ----------------------
% 7.49/2.75  #Ref     : 7
% 7.49/2.75  #Sup     : 1352
% 7.49/2.75  #Fact    : 0
% 7.49/2.75  #Define  : 0
% 7.49/2.75  #Split   : 58
% 7.49/2.75  #Chain   : 0
% 7.49/2.75  #Close   : 0
% 7.49/2.75  
% 7.49/2.75  Ordering : KBO
% 7.49/2.75  
% 7.49/2.75  Simplification rules
% 7.49/2.75  ----------------------
% 7.49/2.75  #Subsume      : 450
% 7.49/2.75  #Demod        : 2472
% 7.49/2.75  #Tautology    : 373
% 7.49/2.75  #SimpNegUnit  : 114
% 7.49/2.75  #BackRed      : 17
% 7.49/2.75  
% 7.49/2.75  #Partial instantiations: 0
% 7.49/2.75  #Strategies tried      : 1
% 7.49/2.75  
% 7.49/2.75  Timing (in seconds)
% 7.49/2.75  ----------------------
% 7.49/2.75  Preprocessing        : 0.40
% 7.49/2.75  Parsing              : 0.21
% 7.49/2.75  CNF conversion       : 0.05
% 7.49/2.75  Main loop            : 1.51
% 7.49/2.75  Inferencing          : 0.50
% 7.49/2.75  Reduction            : 0.58
% 7.49/2.75  Demodulation         : 0.42
% 7.49/2.75  BG Simplification    : 0.04
% 7.49/2.75  Subsumption          : 0.29
% 7.49/2.75  Abstraction          : 0.06
% 7.49/2.75  MUC search           : 0.00
% 7.49/2.75  Cooper               : 0.00
% 7.49/2.75  Total                : 1.96
% 7.49/2.75  Index Insertion      : 0.00
% 7.49/2.75  Index Deletion       : 0.00
% 7.49/2.75  Index Matching       : 0.00
% 7.49/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
