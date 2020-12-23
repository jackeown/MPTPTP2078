%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:37 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  138 (1227 expanded)
%              Number of leaves         :   44 ( 442 expanded)
%              Depth                    :   19
%              Number of atoms          :  282 (5638 expanded)
%              Number of equality atoms :   18 ( 650 expanded)
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

tff(f_223,negated_conjecture,(
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

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_98,axiom,(
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

tff(f_174,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_166,plain,(
    ! [B_419,A_420] :
      ( l1_pre_topc(B_419)
      | ~ m1_pre_topc(B_419,A_420)
      | ~ l1_pre_topc(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_175,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_166])).

tff(c_182,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_175])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_89,plain,(
    ! [A_412] :
      ( u1_struct_0(A_412) = k2_struct_0(A_412)
      | ~ l1_struct_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_93,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_89])).

tff(c_190,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_93])).

tff(c_24,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_207,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_24])).

tff(c_210,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_207])).

tff(c_234,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_237,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_237])).

tff(c_242,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_203,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_50])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_264,plain,(
    ! [B_426,A_427] :
      ( v2_pre_topc(B_426)
      | ~ m1_pre_topc(B_426,A_427)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_273,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_264])).

tff(c_280,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_273])).

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

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_98,plain,(
    ! [A_413] :
      ( u1_struct_0(A_413) = k2_struct_0(A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(resolution,[status(thm)],[c_20,c_89])).

tff(c_106,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_98])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_111,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_56])).

tff(c_202,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_111])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_136,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_54])).

tff(c_201,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_136])).

tff(c_172,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_166])).

tff(c_179,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_172])).

tff(c_186,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_179,c_93])).

tff(c_292,plain,(
    ! [B_434,A_435] :
      ( r1_tarski(u1_struct_0(B_434),u1_struct_0(A_435))
      | ~ m1_pre_topc(B_434,A_435)
      | ~ l1_pre_topc(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_300,plain,(
    ! [B_434] :
      ( r1_tarski(u1_struct_0(B_434),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_434,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_292])).

tff(c_328,plain,(
    ! [B_436] :
      ( r1_tarski(u1_struct_0(B_436),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_436,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_300])).

tff(c_336,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_328])).

tff(c_428,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_32,plain,(
    ! [A_23] :
      ( m1_pre_topc(A_23,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_191,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_52])).

tff(c_430,plain,(
    ! [A_444,B_445] :
      ( m1_pre_topc(A_444,g1_pre_topc(u1_struct_0(B_445),u1_pre_topc(B_445)))
      | ~ m1_pre_topc(A_444,B_445)
      | ~ l1_pre_topc(B_445)
      | ~ l1_pre_topc(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_448,plain,(
    ! [A_444] :
      ( m1_pre_topc(A_444,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_444,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_430])).

tff(c_469,plain,(
    ! [A_446] :
      ( m1_pre_topc(A_446,'#skF_4')
      | ~ m1_pre_topc(A_446,'#skF_3')
      | ~ l1_pre_topc(A_446) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_191,c_448])).

tff(c_473,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_469])).

tff(c_476,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_473])).

tff(c_478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_428,c_476])).

tff(c_480,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_479,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_579,plain,(
    ! [A_451,B_452] :
      ( m1_pre_topc(A_451,B_452)
      | ~ m1_pre_topc(A_451,g1_pre_topc(u1_struct_0(B_452),u1_pre_topc(B_452)))
      | ~ l1_pre_topc(B_452)
      | ~ l1_pre_topc(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_592,plain,(
    ! [A_451] :
      ( m1_pre_topc(A_451,'#skF_3')
      | ~ m1_pre_topc(A_451,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_451) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_579])).

tff(c_616,plain,(
    ! [A_453] :
      ( m1_pre_topc(A_453,'#skF_3')
      | ~ m1_pre_topc(A_453,'#skF_4')
      | ~ l1_pre_topc(A_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_191,c_592])).

tff(c_306,plain,(
    ! [B_434] :
      ( r1_tarski(u1_struct_0(B_434),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_434,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_292])).

tff(c_390,plain,(
    ! [B_439] :
      ( r1_tarski(u1_struct_0(B_439),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_439,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_306])).

tff(c_395,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_390])).

tff(c_569,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_622,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_616,c_569])).

tff(c_646,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_622])).

tff(c_664,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_646])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_664])).

tff(c_669,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_709,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_669,c_2])).

tff(c_712,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_709])).

tff(c_720,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_186])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_223])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_1011,plain,(
    ! [H_482,E_479,D_478,C_481,B_476,A_477,F_480] :
      ( r1_tmap_1(D_478,B_476,E_479,H_482)
      | ~ r1_tmap_1(C_481,B_476,k3_tmap_1(A_477,B_476,D_478,C_481,E_479),H_482)
      | ~ r1_tarski(F_480,u1_struct_0(C_481))
      | ~ r2_hidden(H_482,F_480)
      | ~ v3_pre_topc(F_480,D_478)
      | ~ m1_subset_1(H_482,u1_struct_0(C_481))
      | ~ m1_subset_1(H_482,u1_struct_0(D_478))
      | ~ m1_subset_1(F_480,k1_zfmisc_1(u1_struct_0(D_478)))
      | ~ m1_pre_topc(C_481,D_478)
      | ~ m1_subset_1(E_479,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_478),u1_struct_0(B_476))))
      | ~ v1_funct_2(E_479,u1_struct_0(D_478),u1_struct_0(B_476))
      | ~ v1_funct_1(E_479)
      | ~ m1_pre_topc(D_478,A_477)
      | v2_struct_0(D_478)
      | ~ m1_pre_topc(C_481,A_477)
      | v2_struct_0(C_481)
      | ~ l1_pre_topc(B_476)
      | ~ v2_pre_topc(B_476)
      | v2_struct_0(B_476)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1013,plain,(
    ! [F_480] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_480,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_480)
      | ~ v3_pre_topc(F_480,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_480,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_80,c_1011])).

tff(c_1016,plain,(
    ! [F_480] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_480,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',F_480)
      | ~ v3_pre_topc(F_480,'#skF_4')
      | ~ m1_subset_1(F_480,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_202,c_106,c_190,c_201,c_106,c_190,c_480,c_190,c_203,c_190,c_203,c_720,c_720,c_1013])).

tff(c_1103,plain,(
    ! [F_487] :
      ( ~ r1_tarski(F_487,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',F_487)
      | ~ v3_pre_topc(F_487,'#skF_4')
      | ~ m1_subset_1(F_487,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_42,c_1016])).

tff(c_1110,plain,(
    ! [A_489] :
      ( ~ r2_hidden('#skF_6',A_489)
      | ~ v3_pre_topc(A_489,'#skF_4')
      | ~ r1_tarski(A_489,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1103])).

tff(c_1123,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1110])).

tff(c_1124,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1123])).

tff(c_1127,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1124])).

tff(c_1131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_182,c_1127])).

tff(c_1132,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1123])).

tff(c_1136,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_1132])).

tff(c_1139,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1136])).

tff(c_1141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_1139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:26:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.58  
% 3.70/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.58  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.70/1.58  
% 3.70/1.58  %Foreground sorts:
% 3.70/1.58  
% 3.70/1.58  
% 3.70/1.58  %Background operators:
% 3.70/1.58  
% 3.70/1.58  
% 3.70/1.58  %Foreground operators:
% 3.70/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.70/1.58  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.70/1.58  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.70/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.58  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.58  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.70/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.58  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.70/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.70/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.70/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.70/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.70/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.70/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.70/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.58  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.70/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.58  
% 3.70/1.61  tff(f_223, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.70/1.61  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.70/1.61  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.70/1.61  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.70/1.61  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.70/1.61  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.70/1.61  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.70/1.61  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.70/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.70/1.61  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.61  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.70/1.61  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.70/1.61  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.70/1.61  tff(f_174, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.70/1.61  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_166, plain, (![B_419, A_420]: (l1_pre_topc(B_419) | ~m1_pre_topc(B_419, A_420) | ~l1_pre_topc(A_420))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.61  tff(c_175, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_166])).
% 3.70/1.61  tff(c_182, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_175])).
% 3.70/1.61  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.70/1.61  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_89, plain, (![A_412]: (u1_struct_0(A_412)=k2_struct_0(A_412) | ~l1_struct_0(A_412))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.70/1.61  tff(c_93, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_20, c_89])).
% 3.70/1.61  tff(c_190, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_182, c_93])).
% 3.70/1.61  tff(c_24, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.70/1.61  tff(c_207, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_190, c_24])).
% 3.70/1.61  tff(c_210, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_62, c_207])).
% 3.70/1.61  tff(c_234, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_210])).
% 3.70/1.61  tff(c_237, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_234])).
% 3.70/1.61  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_237])).
% 3.70/1.61  tff(c_242, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_210])).
% 3.70/1.61  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_203, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_50])).
% 3.70/1.61  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.70/1.61  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_264, plain, (![B_426, A_427]: (v2_pre_topc(B_426) | ~m1_pre_topc(B_426, A_427) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.70/1.61  tff(c_273, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_264])).
% 3.70/1.61  tff(c_280, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_273])).
% 3.70/1.61  tff(c_30, plain, (![A_22]: (v3_pre_topc(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.70/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.61  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.70/1.61  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_98, plain, (![A_413]: (u1_struct_0(A_413)=k2_struct_0(A_413) | ~l1_pre_topc(A_413))), inference(resolution, [status(thm)], [c_20, c_89])).
% 3.70/1.61  tff(c_106, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_98])).
% 3.70/1.61  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_111, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_56])).
% 3.70/1.61  tff(c_202, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_111])).
% 3.70/1.61  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_136, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_54])).
% 3.70/1.61  tff(c_201, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_136])).
% 3.70/1.61  tff(c_172, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_166])).
% 3.70/1.61  tff(c_179, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_172])).
% 3.70/1.61  tff(c_186, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_179, c_93])).
% 3.70/1.61  tff(c_292, plain, (![B_434, A_435]: (r1_tarski(u1_struct_0(B_434), u1_struct_0(A_435)) | ~m1_pre_topc(B_434, A_435) | ~l1_pre_topc(A_435))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.70/1.61  tff(c_300, plain, (![B_434]: (r1_tarski(u1_struct_0(B_434), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_434, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_292])).
% 3.70/1.61  tff(c_328, plain, (![B_436]: (r1_tarski(u1_struct_0(B_436), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_436, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_300])).
% 3.70/1.61  tff(c_336, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_186, c_328])).
% 3.70/1.61  tff(c_428, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_336])).
% 3.70/1.61  tff(c_32, plain, (![A_23]: (m1_pre_topc(A_23, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.70/1.61  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_191, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_186, c_52])).
% 3.70/1.61  tff(c_430, plain, (![A_444, B_445]: (m1_pre_topc(A_444, g1_pre_topc(u1_struct_0(B_445), u1_pre_topc(B_445))) | ~m1_pre_topc(A_444, B_445) | ~l1_pre_topc(B_445) | ~l1_pre_topc(A_444))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.70/1.61  tff(c_448, plain, (![A_444]: (m1_pre_topc(A_444, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_444, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_444))), inference(superposition, [status(thm), theory('equality')], [c_186, c_430])).
% 3.70/1.61  tff(c_469, plain, (![A_446]: (m1_pre_topc(A_446, '#skF_4') | ~m1_pre_topc(A_446, '#skF_3') | ~l1_pre_topc(A_446))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_191, c_448])).
% 3.70/1.61  tff(c_473, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_469])).
% 3.70/1.61  tff(c_476, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_473])).
% 3.70/1.61  tff(c_478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_428, c_476])).
% 3.70/1.61  tff(c_480, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_336])).
% 3.70/1.61  tff(c_479, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_336])).
% 3.70/1.61  tff(c_579, plain, (![A_451, B_452]: (m1_pre_topc(A_451, B_452) | ~m1_pre_topc(A_451, g1_pre_topc(u1_struct_0(B_452), u1_pre_topc(B_452))) | ~l1_pre_topc(B_452) | ~l1_pre_topc(A_451))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.70/1.61  tff(c_592, plain, (![A_451]: (m1_pre_topc(A_451, '#skF_3') | ~m1_pre_topc(A_451, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_451))), inference(superposition, [status(thm), theory('equality')], [c_186, c_579])).
% 3.70/1.61  tff(c_616, plain, (![A_453]: (m1_pre_topc(A_453, '#skF_3') | ~m1_pre_topc(A_453, '#skF_4') | ~l1_pre_topc(A_453))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_191, c_592])).
% 3.70/1.61  tff(c_306, plain, (![B_434]: (r1_tarski(u1_struct_0(B_434), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_434, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_292])).
% 3.70/1.61  tff(c_390, plain, (![B_439]: (r1_tarski(u1_struct_0(B_439), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_439, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_306])).
% 3.70/1.61  tff(c_395, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_190, c_390])).
% 3.70/1.61  tff(c_569, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_395])).
% 3.70/1.61  tff(c_622, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_616, c_569])).
% 3.70/1.61  tff(c_646, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_622])).
% 3.70/1.61  tff(c_664, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_32, c_646])).
% 3.70/1.61  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_664])).
% 3.70/1.61  tff(c_669, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_395])).
% 3.70/1.61  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.61  tff(c_709, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_669, c_2])).
% 3.70/1.61  tff(c_712, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_709])).
% 3.70/1.61  tff(c_720, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_712, c_186])).
% 3.70/1.61  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_223])).
% 3.70/1.61  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 3.70/1.61  tff(c_1011, plain, (![H_482, E_479, D_478, C_481, B_476, A_477, F_480]: (r1_tmap_1(D_478, B_476, E_479, H_482) | ~r1_tmap_1(C_481, B_476, k3_tmap_1(A_477, B_476, D_478, C_481, E_479), H_482) | ~r1_tarski(F_480, u1_struct_0(C_481)) | ~r2_hidden(H_482, F_480) | ~v3_pre_topc(F_480, D_478) | ~m1_subset_1(H_482, u1_struct_0(C_481)) | ~m1_subset_1(H_482, u1_struct_0(D_478)) | ~m1_subset_1(F_480, k1_zfmisc_1(u1_struct_0(D_478))) | ~m1_pre_topc(C_481, D_478) | ~m1_subset_1(E_479, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_478), u1_struct_0(B_476)))) | ~v1_funct_2(E_479, u1_struct_0(D_478), u1_struct_0(B_476)) | ~v1_funct_1(E_479) | ~m1_pre_topc(D_478, A_477) | v2_struct_0(D_478) | ~m1_pre_topc(C_481, A_477) | v2_struct_0(C_481) | ~l1_pre_topc(B_476) | ~v2_pre_topc(B_476) | v2_struct_0(B_476) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477))), inference(cnfTransformation, [status(thm)], [f_174])).
% 3.70/1.61  tff(c_1013, plain, (![F_480]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_480, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_480) | ~v3_pre_topc(F_480, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_480, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_1011])).
% 3.70/1.61  tff(c_1016, plain, (![F_480]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_480, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', F_480) | ~v3_pre_topc(F_480, '#skF_4') | ~m1_subset_1(F_480, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_202, c_106, c_190, c_201, c_106, c_190, c_480, c_190, c_203, c_190, c_203, c_720, c_720, c_1013])).
% 3.70/1.61  tff(c_1103, plain, (![F_487]: (~r1_tarski(F_487, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', F_487) | ~v3_pre_topc(F_487, '#skF_4') | ~m1_subset_1(F_487, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_42, c_1016])).
% 3.70/1.61  tff(c_1110, plain, (![A_489]: (~r2_hidden('#skF_6', A_489) | ~v3_pre_topc(A_489, '#skF_4') | ~r1_tarski(A_489, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_1103])).
% 3.70/1.61  tff(c_1123, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6, c_1110])).
% 3.70/1.61  tff(c_1124, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1123])).
% 3.70/1.61  tff(c_1127, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1124])).
% 3.70/1.61  tff(c_1131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_182, c_1127])).
% 3.70/1.61  tff(c_1132, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1123])).
% 3.70/1.61  tff(c_1136, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_1132])).
% 3.70/1.61  tff(c_1139, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1136])).
% 3.70/1.61  tff(c_1141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_1139])).
% 3.70/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.61  
% 3.70/1.61  Inference rules
% 3.70/1.61  ----------------------
% 3.70/1.61  #Ref     : 0
% 3.70/1.61  #Sup     : 220
% 3.70/1.61  #Fact    : 0
% 3.70/1.61  #Define  : 0
% 3.70/1.61  #Split   : 20
% 3.70/1.61  #Chain   : 0
% 3.70/1.61  #Close   : 0
% 3.70/1.61  
% 3.70/1.61  Ordering : KBO
% 3.70/1.61  
% 3.70/1.61  Simplification rules
% 3.70/1.61  ----------------------
% 3.70/1.61  #Subsume      : 27
% 3.70/1.61  #Demod        : 208
% 3.70/1.61  #Tautology    : 75
% 3.70/1.61  #SimpNegUnit  : 18
% 3.70/1.61  #BackRed      : 14
% 3.70/1.61  
% 3.70/1.61  #Partial instantiations: 0
% 3.70/1.61  #Strategies tried      : 1
% 3.70/1.61  
% 3.70/1.61  Timing (in seconds)
% 3.70/1.61  ----------------------
% 3.70/1.61  Preprocessing        : 0.39
% 3.70/1.61  Parsing              : 0.20
% 3.70/1.61  CNF conversion       : 0.05
% 3.70/1.61  Main loop            : 0.46
% 3.70/1.61  Inferencing          : 0.14
% 3.70/1.61  Reduction            : 0.16
% 3.70/1.61  Demodulation         : 0.11
% 3.70/1.61  BG Simplification    : 0.02
% 3.70/1.61  Subsumption          : 0.10
% 3.70/1.61  Abstraction          : 0.02
% 3.70/1.61  MUC search           : 0.00
% 3.70/1.61  Cooper               : 0.00
% 3.70/1.61  Total                : 0.90
% 3.70/1.61  Index Insertion      : 0.00
% 3.70/1.61  Index Deletion       : 0.00
% 3.70/1.61  Index Matching       : 0.00
% 3.70/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
