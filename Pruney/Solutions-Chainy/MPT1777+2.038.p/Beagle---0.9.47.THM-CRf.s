%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:37 EST 2020

% Result     : Theorem 4.86s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :  148 (1384 expanded)
%              Number of leaves         :   46 ( 497 expanded)
%              Depth                    :   20
%              Number of atoms          :  323 (6420 expanded)
%              Number of equality atoms :   18 ( 728 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

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

tff(f_240,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_124,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_117,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_191,axiom,(
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
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_118,plain,(
    ! [B_421,A_422] :
      ( l1_pre_topc(B_421)
      | ~ m1_pre_topc(B_421,A_422)
      | ~ l1_pre_topc(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_127,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_118])).

tff(c_134,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_127])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_91,plain,(
    ! [A_419] :
      ( u1_struct_0(A_419) = k2_struct_0(A_419)
      | ~ l1_struct_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_95,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_142,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_134,c_95])).

tff(c_161,plain,(
    ! [A_423] :
      ( ~ v1_xboole_0(u1_struct_0(A_423))
      | ~ l1_struct_0(A_423)
      | v2_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_164,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_161])).

tff(c_174,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_164])).

tff(c_178,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_181,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_178])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_181])).

tff(c_186,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_152,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_52])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_261,plain,(
    ! [B_435,A_436] :
      ( v2_pre_topc(B_435)
      | ~ m1_pre_topc(B_435,A_436)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_270,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_261])).

tff(c_277,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_270])).

tff(c_30,plain,(
    ! [A_22] :
      ( v3_pre_topc(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_100,plain,(
    ! [A_420] :
      ( u1_struct_0(A_420) = k2_struct_0(A_420)
      | ~ l1_pre_topc(A_420) ) ),
    inference(resolution,[status(thm)],[c_20,c_91])).

tff(c_107,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_100])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_109,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_58])).

tff(c_151,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_109])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_149,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_56])).

tff(c_150,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_149])).

tff(c_124,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_118])).

tff(c_131,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_124])).

tff(c_138,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_95])).

tff(c_278,plain,(
    ! [B_437,A_438] :
      ( r1_tarski(u1_struct_0(B_437),u1_struct_0(A_438))
      | ~ m1_pre_topc(B_437,A_438)
      | ~ l1_pre_topc(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_286,plain,(
    ! [B_437] :
      ( r1_tarski(u1_struct_0(B_437),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_437,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_278])).

tff(c_321,plain,(
    ! [B_442] :
      ( r1_tarski(u1_struct_0(B_442),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_442,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_286])).

tff(c_329,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_321])).

tff(c_434,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_34,plain,(
    ! [A_30] :
      ( m1_pre_topc(A_30,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_143,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_54])).

tff(c_435,plain,(
    ! [A_450,B_451] :
      ( m1_pre_topc(A_450,g1_pre_topc(u1_struct_0(B_451),u1_pre_topc(B_451)))
      | ~ m1_pre_topc(A_450,B_451)
      | ~ l1_pre_topc(B_451)
      | ~ l1_pre_topc(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_449,plain,(
    ! [A_450] :
      ( m1_pre_topc(A_450,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_450,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_435])).

tff(c_473,plain,(
    ! [A_452] :
      ( m1_pre_topc(A_452,'#skF_4')
      | ~ m1_pre_topc(A_452,'#skF_3')
      | ~ l1_pre_topc(A_452) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_143,c_449])).

tff(c_481,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_473])).

tff(c_488,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_481])).

tff(c_490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_488])).

tff(c_492,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_491,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_583,plain,(
    ! [A_460,B_461] :
      ( m1_pre_topc(A_460,B_461)
      | ~ m1_pre_topc(A_460,g1_pre_topc(u1_struct_0(B_461),u1_pre_topc(B_461)))
      | ~ l1_pre_topc(B_461)
      | ~ l1_pre_topc(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_596,plain,(
    ! [A_460] :
      ( m1_pre_topc(A_460,'#skF_3')
      | ~ m1_pre_topc(A_460,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_583])).

tff(c_620,plain,(
    ! [A_462] :
      ( m1_pre_topc(A_462,'#skF_3')
      | ~ m1_pre_topc(A_462,'#skF_4')
      | ~ l1_pre_topc(A_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_143,c_596])).

tff(c_292,plain,(
    ! [B_437] :
      ( r1_tarski(u1_struct_0(B_437),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_437,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_278])).

tff(c_383,plain,(
    ! [B_445] :
      ( r1_tarski(u1_struct_0(B_445),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_445,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_292])).

tff(c_388,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_383])).

tff(c_575,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_626,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_620,c_575])).

tff(c_650,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_626])).

tff(c_668,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_650])).

tff(c_672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_668])).

tff(c_673,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_713,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_673,c_2])).

tff(c_716,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_713])).

tff(c_724,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_716,c_138])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1033,plain,(
    ! [C_487,A_481,H_482,B_486,D_484,F_483,E_485] :
      ( r1_tmap_1(D_484,B_486,E_485,H_482)
      | ~ r1_tmap_1(C_487,B_486,k3_tmap_1(A_481,B_486,D_484,C_487,E_485),H_482)
      | ~ m1_connsp_2(F_483,D_484,H_482)
      | ~ r1_tarski(F_483,u1_struct_0(C_487))
      | ~ m1_subset_1(H_482,u1_struct_0(C_487))
      | ~ m1_subset_1(H_482,u1_struct_0(D_484))
      | ~ m1_subset_1(F_483,k1_zfmisc_1(u1_struct_0(D_484)))
      | ~ m1_pre_topc(C_487,D_484)
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_484),u1_struct_0(B_486))))
      | ~ v1_funct_2(E_485,u1_struct_0(D_484),u1_struct_0(B_486))
      | ~ v1_funct_1(E_485)
      | ~ m1_pre_topc(D_484,A_481)
      | v2_struct_0(D_484)
      | ~ m1_pre_topc(C_487,A_481)
      | v2_struct_0(C_487)
      | ~ l1_pre_topc(B_486)
      | ~ v2_pre_topc(B_486)
      | v2_struct_0(B_486)
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1035,plain,(
    ! [F_483] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_483,'#skF_4','#skF_6')
      | ~ r1_tarski(F_483,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_483,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_82,c_1033])).

tff(c_1038,plain,(
    ! [F_483] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_483,'#skF_4','#skF_6')
      | ~ r1_tarski(F_483,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(F_483,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_151,c_107,c_142,c_150,c_107,c_142,c_492,c_142,c_152,c_142,c_152,c_724,c_724,c_1035])).

tff(c_1091,plain,(
    ! [F_492] :
      ( ~ m1_connsp_2(F_492,'#skF_4','#skF_6')
      | ~ r1_tarski(F_492,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(F_492,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_1038])).

tff(c_1097,plain,(
    ! [A_493] :
      ( ~ m1_connsp_2(A_493,'#skF_4','#skF_6')
      | ~ r1_tarski(A_493,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1091])).

tff(c_1110,plain,(
    ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_1097])).

tff(c_866,plain,(
    ! [B_470,A_471,C_472] :
      ( m1_connsp_2(B_470,A_471,C_472)
      | ~ r2_hidden(C_472,B_470)
      | ~ v3_pre_topc(B_470,A_471)
      | ~ m1_subset_1(C_472,u1_struct_0(A_471))
      | ~ m1_subset_1(B_470,k1_zfmisc_1(u1_struct_0(A_471)))
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | v2_struct_0(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_870,plain,(
    ! [B_470,C_472] :
      ( m1_connsp_2(B_470,'#skF_4',C_472)
      | ~ r2_hidden(C_472,B_470)
      | ~ v3_pre_topc(B_470,'#skF_4')
      | ~ m1_subset_1(C_472,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_470,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_866])).

tff(c_879,plain,(
    ! [B_470,C_472] :
      ( m1_connsp_2(B_470,'#skF_4',C_472)
      | ~ r2_hidden(C_472,B_470)
      | ~ v3_pre_topc(B_470,'#skF_4')
      | ~ m1_subset_1(C_472,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_470,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_134,c_142,c_870])).

tff(c_1244,plain,(
    ! [B_507,C_508] :
      ( m1_connsp_2(B_507,'#skF_4',C_508)
      | ~ r2_hidden(C_508,B_507)
      | ~ v3_pre_topc(B_507,'#skF_4')
      | ~ m1_subset_1(C_508,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_507,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_879])).

tff(c_1848,plain,(
    ! [B_533] :
      ( m1_connsp_2(B_533,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_533)
      | ~ v3_pre_topc(B_533,'#skF_4')
      | ~ m1_subset_1(B_533,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_152,c_1244])).

tff(c_2427,plain,(
    ! [A_564] :
      ( m1_connsp_2(A_564,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',A_564)
      | ~ v3_pre_topc(A_564,'#skF_4')
      | ~ r1_tarski(A_564,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1848])).

tff(c_2437,plain,
    ( m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_2427])).

tff(c_2442,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1110,c_2437])).

tff(c_2443,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2442])).

tff(c_2446,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_2443])).

tff(c_2450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_134,c_2446])).

tff(c_2451,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2442])).

tff(c_2455,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_2451])).

tff(c_2458,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2455])).

tff(c_2460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_2458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.86/1.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.87  
% 4.86/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.87  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.86/1.87  
% 4.86/1.87  %Foreground sorts:
% 4.86/1.87  
% 4.86/1.87  
% 4.86/1.87  %Background operators:
% 4.86/1.87  
% 4.86/1.87  
% 4.86/1.87  %Foreground operators:
% 4.86/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.86/1.87  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.86/1.87  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.86/1.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.86/1.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.86/1.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.86/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.86/1.87  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.86/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.86/1.87  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.86/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.86/1.87  tff('#skF_7', type, '#skF_7': $i).
% 4.86/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.86/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.86/1.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.86/1.87  tff('#skF_6', type, '#skF_6': $i).
% 4.86/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.86/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.86/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.86/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.86/1.87  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.86/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.86/1.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.86/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.86/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.86/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.86/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.86/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.86/1.87  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.86/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.86/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.86/1.87  
% 4.86/1.90  tff(f_240, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.86/1.90  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.86/1.90  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.86/1.90  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.86/1.90  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.86/1.90  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.86/1.90  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.86/1.90  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.86/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.86/1.90  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.86/1.90  tff(f_124, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.86/1.90  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.86/1.90  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.86/1.90  tff(f_191, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.86/1.90  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.86/1.90  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_118, plain, (![B_421, A_422]: (l1_pre_topc(B_421) | ~m1_pre_topc(B_421, A_422) | ~l1_pre_topc(A_422))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.86/1.90  tff(c_127, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_118])).
% 4.86/1.90  tff(c_134, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_127])).
% 4.86/1.90  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.86/1.90  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_91, plain, (![A_419]: (u1_struct_0(A_419)=k2_struct_0(A_419) | ~l1_struct_0(A_419))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.86/1.90  tff(c_95, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_20, c_91])).
% 4.86/1.90  tff(c_142, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_134, c_95])).
% 4.86/1.90  tff(c_161, plain, (![A_423]: (~v1_xboole_0(u1_struct_0(A_423)) | ~l1_struct_0(A_423) | v2_struct_0(A_423))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.86/1.90  tff(c_164, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_142, c_161])).
% 4.86/1.90  tff(c_174, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_164])).
% 4.86/1.90  tff(c_178, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_174])).
% 4.86/1.90  tff(c_181, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_178])).
% 4.86/1.90  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_181])).
% 4.86/1.90  tff(c_186, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_174])).
% 4.86/1.90  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_152, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_52])).
% 4.86/1.90  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.86/1.90  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_261, plain, (![B_435, A_436]: (v2_pre_topc(B_435) | ~m1_pre_topc(B_435, A_436) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.86/1.90  tff(c_270, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_261])).
% 4.86/1.90  tff(c_277, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_270])).
% 4.86/1.90  tff(c_30, plain, (![A_22]: (v3_pre_topc(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.86/1.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/1.90  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.86/1.90  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_100, plain, (![A_420]: (u1_struct_0(A_420)=k2_struct_0(A_420) | ~l1_pre_topc(A_420))), inference(resolution, [status(thm)], [c_20, c_91])).
% 4.86/1.90  tff(c_107, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_100])).
% 4.86/1.90  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_109, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_58])).
% 4.86/1.90  tff(c_151, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_109])).
% 4.86/1.90  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_149, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_56])).
% 4.86/1.90  tff(c_150, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_149])).
% 4.86/1.90  tff(c_124, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_118])).
% 4.86/1.90  tff(c_131, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_124])).
% 4.86/1.90  tff(c_138, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_131, c_95])).
% 4.86/1.90  tff(c_278, plain, (![B_437, A_438]: (r1_tarski(u1_struct_0(B_437), u1_struct_0(A_438)) | ~m1_pre_topc(B_437, A_438) | ~l1_pre_topc(A_438))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.86/1.90  tff(c_286, plain, (![B_437]: (r1_tarski(u1_struct_0(B_437), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_437, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_278])).
% 4.86/1.90  tff(c_321, plain, (![B_442]: (r1_tarski(u1_struct_0(B_442), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_442, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_286])).
% 4.86/1.90  tff(c_329, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_138, c_321])).
% 4.86/1.90  tff(c_434, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_329])).
% 4.86/1.90  tff(c_34, plain, (![A_30]: (m1_pre_topc(A_30, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.86/1.90  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_143, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_54])).
% 4.86/1.90  tff(c_435, plain, (![A_450, B_451]: (m1_pre_topc(A_450, g1_pre_topc(u1_struct_0(B_451), u1_pre_topc(B_451))) | ~m1_pre_topc(A_450, B_451) | ~l1_pre_topc(B_451) | ~l1_pre_topc(A_450))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.86/1.90  tff(c_449, plain, (![A_450]: (m1_pre_topc(A_450, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_450, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_450))), inference(superposition, [status(thm), theory('equality')], [c_138, c_435])).
% 4.86/1.90  tff(c_473, plain, (![A_452]: (m1_pre_topc(A_452, '#skF_4') | ~m1_pre_topc(A_452, '#skF_3') | ~l1_pre_topc(A_452))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_143, c_449])).
% 4.86/1.90  tff(c_481, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_473])).
% 4.86/1.90  tff(c_488, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_481])).
% 4.86/1.90  tff(c_490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_488])).
% 4.86/1.90  tff(c_492, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_329])).
% 4.86/1.90  tff(c_491, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_329])).
% 4.86/1.90  tff(c_583, plain, (![A_460, B_461]: (m1_pre_topc(A_460, B_461) | ~m1_pre_topc(A_460, g1_pre_topc(u1_struct_0(B_461), u1_pre_topc(B_461))) | ~l1_pre_topc(B_461) | ~l1_pre_topc(A_460))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.86/1.90  tff(c_596, plain, (![A_460]: (m1_pre_topc(A_460, '#skF_3') | ~m1_pre_topc(A_460, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_460))), inference(superposition, [status(thm), theory('equality')], [c_138, c_583])).
% 4.86/1.90  tff(c_620, plain, (![A_462]: (m1_pre_topc(A_462, '#skF_3') | ~m1_pre_topc(A_462, '#skF_4') | ~l1_pre_topc(A_462))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_143, c_596])).
% 4.86/1.90  tff(c_292, plain, (![B_437]: (r1_tarski(u1_struct_0(B_437), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_437, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_138, c_278])).
% 4.86/1.90  tff(c_383, plain, (![B_445]: (r1_tarski(u1_struct_0(B_445), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_445, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_292])).
% 4.86/1.90  tff(c_388, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_142, c_383])).
% 4.86/1.90  tff(c_575, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_388])).
% 4.86/1.90  tff(c_626, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_620, c_575])).
% 4.86/1.90  tff(c_650, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_626])).
% 4.86/1.90  tff(c_668, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34, c_650])).
% 4.86/1.90  tff(c_672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_668])).
% 4.86/1.90  tff(c_673, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_388])).
% 4.86/1.90  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/1.90  tff(c_713, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_673, c_2])).
% 4.86/1.90  tff(c_716, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_491, c_713])).
% 4.86/1.90  tff(c_724, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_716, c_138])).
% 4.86/1.90  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_240])).
% 4.86/1.90  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 4.86/1.90  tff(c_1033, plain, (![C_487, A_481, H_482, B_486, D_484, F_483, E_485]: (r1_tmap_1(D_484, B_486, E_485, H_482) | ~r1_tmap_1(C_487, B_486, k3_tmap_1(A_481, B_486, D_484, C_487, E_485), H_482) | ~m1_connsp_2(F_483, D_484, H_482) | ~r1_tarski(F_483, u1_struct_0(C_487)) | ~m1_subset_1(H_482, u1_struct_0(C_487)) | ~m1_subset_1(H_482, u1_struct_0(D_484)) | ~m1_subset_1(F_483, k1_zfmisc_1(u1_struct_0(D_484))) | ~m1_pre_topc(C_487, D_484) | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_484), u1_struct_0(B_486)))) | ~v1_funct_2(E_485, u1_struct_0(D_484), u1_struct_0(B_486)) | ~v1_funct_1(E_485) | ~m1_pre_topc(D_484, A_481) | v2_struct_0(D_484) | ~m1_pre_topc(C_487, A_481) | v2_struct_0(C_487) | ~l1_pre_topc(B_486) | ~v2_pre_topc(B_486) | v2_struct_0(B_486) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(cnfTransformation, [status(thm)], [f_191])).
% 4.86/1.90  tff(c_1035, plain, (![F_483]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_483, '#skF_4', '#skF_6') | ~r1_tarski(F_483, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_483, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_82, c_1033])).
% 4.86/1.90  tff(c_1038, plain, (![F_483]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_483, '#skF_4', '#skF_6') | ~r1_tarski(F_483, k2_struct_0('#skF_4')) | ~m1_subset_1(F_483, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_151, c_107, c_142, c_150, c_107, c_142, c_492, c_142, c_152, c_142, c_152, c_724, c_724, c_1035])).
% 4.86/1.90  tff(c_1091, plain, (![F_492]: (~m1_connsp_2(F_492, '#skF_4', '#skF_6') | ~r1_tarski(F_492, k2_struct_0('#skF_4')) | ~m1_subset_1(F_492, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_1038])).
% 4.86/1.90  tff(c_1097, plain, (![A_493]: (~m1_connsp_2(A_493, '#skF_4', '#skF_6') | ~r1_tarski(A_493, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_1091])).
% 4.86/1.90  tff(c_1110, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_1097])).
% 4.86/1.90  tff(c_866, plain, (![B_470, A_471, C_472]: (m1_connsp_2(B_470, A_471, C_472) | ~r2_hidden(C_472, B_470) | ~v3_pre_topc(B_470, A_471) | ~m1_subset_1(C_472, u1_struct_0(A_471)) | ~m1_subset_1(B_470, k1_zfmisc_1(u1_struct_0(A_471))) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | v2_struct_0(A_471))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.86/1.90  tff(c_870, plain, (![B_470, C_472]: (m1_connsp_2(B_470, '#skF_4', C_472) | ~r2_hidden(C_472, B_470) | ~v3_pre_topc(B_470, '#skF_4') | ~m1_subset_1(C_472, k2_struct_0('#skF_4')) | ~m1_subset_1(B_470, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_866])).
% 4.86/1.90  tff(c_879, plain, (![B_470, C_472]: (m1_connsp_2(B_470, '#skF_4', C_472) | ~r2_hidden(C_472, B_470) | ~v3_pre_topc(B_470, '#skF_4') | ~m1_subset_1(C_472, k2_struct_0('#skF_4')) | ~m1_subset_1(B_470, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_134, c_142, c_870])).
% 4.86/1.90  tff(c_1244, plain, (![B_507, C_508]: (m1_connsp_2(B_507, '#skF_4', C_508) | ~r2_hidden(C_508, B_507) | ~v3_pre_topc(B_507, '#skF_4') | ~m1_subset_1(C_508, k2_struct_0('#skF_4')) | ~m1_subset_1(B_507, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_879])).
% 4.86/1.90  tff(c_1848, plain, (![B_533]: (m1_connsp_2(B_533, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_533) | ~v3_pre_topc(B_533, '#skF_4') | ~m1_subset_1(B_533, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_152, c_1244])).
% 4.86/1.90  tff(c_2427, plain, (![A_564]: (m1_connsp_2(A_564, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', A_564) | ~v3_pre_topc(A_564, '#skF_4') | ~r1_tarski(A_564, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_1848])).
% 4.86/1.90  tff(c_2437, plain, (m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6, c_2427])).
% 4.86/1.90  tff(c_2442, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1110, c_2437])).
% 4.86/1.90  tff(c_2443, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2442])).
% 4.86/1.90  tff(c_2446, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_2443])).
% 4.86/1.90  tff(c_2450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_277, c_134, c_2446])).
% 4.86/1.90  tff(c_2451, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_2442])).
% 4.86/1.90  tff(c_2455, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_2451])).
% 4.86/1.90  tff(c_2458, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2455])).
% 4.86/1.90  tff(c_2460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_2458])).
% 4.86/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.90  
% 4.86/1.90  Inference rules
% 4.86/1.90  ----------------------
% 4.86/1.90  #Ref     : 0
% 4.86/1.90  #Sup     : 475
% 4.86/1.90  #Fact    : 0
% 4.86/1.90  #Define  : 0
% 4.86/1.90  #Split   : 25
% 4.86/1.90  #Chain   : 0
% 4.86/1.90  #Close   : 0
% 4.86/1.90  
% 4.86/1.90  Ordering : KBO
% 4.86/1.90  
% 4.86/1.90  Simplification rules
% 4.86/1.90  ----------------------
% 4.86/1.90  #Subsume      : 149
% 4.86/1.90  #Demod        : 668
% 4.86/1.90  #Tautology    : 147
% 4.86/1.90  #SimpNegUnit  : 36
% 4.86/1.90  #BackRed      : 14
% 4.86/1.90  
% 4.86/1.90  #Partial instantiations: 0
% 4.86/1.90  #Strategies tried      : 1
% 4.86/1.90  
% 4.86/1.90  Timing (in seconds)
% 4.86/1.90  ----------------------
% 4.86/1.90  Preprocessing        : 0.41
% 4.86/1.90  Parsing              : 0.21
% 4.86/1.90  CNF conversion       : 0.05
% 4.86/1.90  Main loop            : 0.69
% 4.86/1.90  Inferencing          : 0.22
% 4.86/1.90  Reduction            : 0.24
% 4.86/1.90  Demodulation         : 0.17
% 4.86/1.90  BG Simplification    : 0.03
% 4.86/1.90  Subsumption          : 0.15
% 4.86/1.90  Abstraction          : 0.03
% 4.86/1.90  MUC search           : 0.00
% 4.86/1.90  Cooper               : 0.00
% 4.86/1.90  Total                : 1.15
% 4.86/1.90  Index Insertion      : 0.00
% 4.86/1.90  Index Deletion       : 0.00
% 4.86/1.90  Index Matching       : 0.00
% 4.86/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
