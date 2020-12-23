%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:32 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :  139 (2023 expanded)
%              Number of leaves         :   48 ( 716 expanded)
%              Depth                    :   23
%              Number of atoms          :  284 (9172 expanded)
%              Number of equality atoms :   37 (1190 expanded)
%              Maximal formula depth    :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_241,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_104,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_192,axiom,(
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

tff(c_84,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_70,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_176,plain,(
    ! [B_426,A_427] :
      ( l1_pre_topc(B_426)
      | ~ m1_pre_topc(B_426,A_427)
      | ~ l1_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_182,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_176])).

tff(c_189,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_182])).

tff(c_26,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_99,plain,(
    ! [A_419] :
      ( u1_struct_0(A_419) = k2_struct_0(A_419)
      | ~ l1_struct_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_103,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_196,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_103])).

tff(c_32,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_207,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_32])).

tff(c_210,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_207])).

tff(c_223,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_226,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_223])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_226])).

tff(c_231,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_203,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_60])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_291,plain,(
    ! [B_438,A_439] :
      ( v2_pre_topc(B_438)
      | ~ m1_pre_topc(B_438,A_439)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_297,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_291])).

tff(c_304,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_297])).

tff(c_42,plain,(
    ! [A_32] :
      ( v3_pre_topc(k2_struct_0(A_32),A_32)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_52,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_80,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_78,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_74,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_108,plain,(
    ! [A_420] :
      ( u1_struct_0(A_420) = k2_struct_0(A_420)
      | ~ l1_pre_topc(A_420) ) ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_116,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_108])).

tff(c_66,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_121,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_66])).

tff(c_202,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_121])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_150,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_64])).

tff(c_201,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_150])).

tff(c_185,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_176])).

tff(c_192,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_185])).

tff(c_44,plain,(
    ! [A_33] :
      ( m1_pre_topc(A_33,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_200,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_192,c_103])).

tff(c_62,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_212,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_62])).

tff(c_322,plain,(
    ! [A_445] :
      ( m1_subset_1(u1_pre_topc(A_445),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_445))))
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_334,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_322])).

tff(c_348,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_334])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( v1_pre_topc(g1_pre_topc(A_15,B_16))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_357,plain,(
    v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_348,c_24])).

tff(c_365,plain,(
    v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_357])).

tff(c_382,plain,(
    ! [A_446] :
      ( g1_pre_topc(u1_struct_0(A_446),u1_pre_topc(A_446)) = A_446
      | ~ v1_pre_topc(A_446)
      | ~ l1_pre_topc(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_394,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_382])).

tff(c_406,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_365,c_394])).

tff(c_612,plain,(
    ! [C_453,A_454,D_455,B_456] :
      ( C_453 = A_454
      | g1_pre_topc(C_453,D_455) != g1_pre_topc(A_454,B_456)
      | ~ m1_subset_1(B_456,k1_zfmisc_1(k1_zfmisc_1(A_454))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_624,plain,(
    ! [C_453,D_455] :
      ( k2_struct_0('#skF_3') = C_453
      | g1_pre_topc(C_453,D_455) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_612])).

tff(c_629,plain,(
    ! [C_457,D_458] :
      ( k2_struct_0('#skF_3') = C_457
      | g1_pre_topc(C_457,D_458) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_624])).

tff(c_639,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_629])).

tff(c_645,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_212])).

tff(c_337,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_322])).

tff(c_350,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_337])).

tff(c_787,plain,(
    ! [D_469,B_470,C_471,A_472] :
      ( D_469 = B_470
      | g1_pre_topc(C_471,D_469) != g1_pre_topc(A_472,B_470)
      | ~ m1_subset_1(B_470,k1_zfmisc_1(k1_zfmisc_1(A_472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_795,plain,(
    ! [D_469,C_471] :
      ( u1_pre_topc('#skF_4') = D_469
      | g1_pre_topc(C_471,D_469) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_787])).

tff(c_804,plain,(
    ! [D_473,C_474] :
      ( u1_pre_topc('#skF_4') = D_473
      | g1_pre_topc(C_474,D_473) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_795])).

tff(c_814,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_804])).

tff(c_648,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_200])).

tff(c_905,plain,(
    ! [A_481,B_482] :
      ( m1_pre_topc(A_481,g1_pre_topc(u1_struct_0(B_482),u1_pre_topc(B_482)))
      | ~ m1_pre_topc(A_481,B_482)
      | ~ l1_pre_topc(B_482)
      | ~ l1_pre_topc(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_923,plain,(
    ! [A_481] :
      ( m1_pre_topc(A_481,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_481,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_481) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_905])).

tff(c_958,plain,(
    ! [A_484] :
      ( m1_pre_topc(A_484,'#skF_4')
      | ~ m1_pre_topc(A_484,'#skF_3')
      | ~ l1_pre_topc(A_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_406,c_814,c_923])).

tff(c_966,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_958])).

tff(c_972,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_966])).

tff(c_56,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_54,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_90,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54])).

tff(c_1363,plain,(
    ! [F_520,C_524,D_521,H_519,E_522,A_518,B_523] :
      ( r1_tmap_1(D_521,B_523,E_522,H_519)
      | ~ r1_tmap_1(C_524,B_523,k3_tmap_1(A_518,B_523,D_521,C_524,E_522),H_519)
      | ~ r1_tarski(F_520,u1_struct_0(C_524))
      | ~ r2_hidden(H_519,F_520)
      | ~ v3_pre_topc(F_520,D_521)
      | ~ m1_subset_1(H_519,u1_struct_0(C_524))
      | ~ m1_subset_1(H_519,u1_struct_0(D_521))
      | ~ m1_subset_1(F_520,k1_zfmisc_1(u1_struct_0(D_521)))
      | ~ m1_pre_topc(C_524,D_521)
      | ~ m1_subset_1(E_522,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_521),u1_struct_0(B_523))))
      | ~ v1_funct_2(E_522,u1_struct_0(D_521),u1_struct_0(B_523))
      | ~ v1_funct_1(E_522)
      | ~ m1_pre_topc(D_521,A_518)
      | v2_struct_0(D_521)
      | ~ m1_pre_topc(C_524,A_518)
      | v2_struct_0(C_524)
      | ~ l1_pre_topc(B_523)
      | ~ v2_pre_topc(B_523)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(A_518)
      | ~ v2_pre_topc(A_518)
      | v2_struct_0(A_518) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1365,plain,(
    ! [F_520] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_520,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_520)
      | ~ v3_pre_topc(F_520,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_520,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_90,c_1363])).

tff(c_1368,plain,(
    ! [F_520] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_520,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',F_520)
      | ~ v3_pre_topc(F_520,'#skF_4')
      | ~ m1_subset_1(F_520,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_74,c_70,c_68,c_202,c_116,c_196,c_201,c_116,c_196,c_972,c_196,c_203,c_196,c_203,c_648,c_648,c_1365])).

tff(c_1376,plain,(
    ! [F_527] :
      ( ~ r1_tarski(F_527,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',F_527)
      | ~ v3_pre_topc(F_527,'#skF_4')
      | ~ m1_subset_1(F_527,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_76,c_72,c_52,c_1368])).

tff(c_1386,plain,(
    ! [A_528] :
      ( ~ r2_hidden('#skF_6',A_528)
      | ~ v3_pre_topc(A_528,'#skF_4')
      | ~ r1_tarski(A_528,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_1376])).

tff(c_1391,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1386])).

tff(c_1392,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1391])).

tff(c_1395,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1392])).

tff(c_1399,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_189,c_1395])).

tff(c_1400,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1391])).

tff(c_1404,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_1400])).

tff(c_1407,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1404])).

tff(c_1409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_1407])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.73  
% 4.38/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.74  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.38/1.74  
% 4.38/1.74  %Foreground sorts:
% 4.38/1.74  
% 4.38/1.74  
% 4.38/1.74  %Background operators:
% 4.38/1.74  
% 4.38/1.74  
% 4.38/1.74  %Foreground operators:
% 4.38/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.38/1.74  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.38/1.74  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.38/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.38/1.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.38/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.74  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.38/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.74  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.38/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.38/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.38/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.38/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.38/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.38/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.38/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.38/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.38/1.74  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.38/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.38/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.38/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.38/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.38/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.74  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.38/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.38/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.38/1.74  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.38/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.38/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.38/1.74  
% 4.38/1.76  tff(f_241, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.38/1.76  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.38/1.76  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.38/1.76  tff(f_66, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.38/1.76  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.38/1.76  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.38/1.76  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.38/1.76  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.38/1.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.38/1.76  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.38/1.76  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.38/1.76  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.38/1.76  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 4.38/1.76  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.38/1.76  tff(f_104, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.38/1.76  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.38/1.76  tff(f_192, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.38/1.76  tff(c_84, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_70, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_176, plain, (![B_426, A_427]: (l1_pre_topc(B_426) | ~m1_pre_topc(B_426, A_427) | ~l1_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.38/1.76  tff(c_182, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_176])).
% 4.38/1.76  tff(c_189, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_182])).
% 4.38/1.76  tff(c_26, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.38/1.76  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_99, plain, (![A_419]: (u1_struct_0(A_419)=k2_struct_0(A_419) | ~l1_struct_0(A_419))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.38/1.76  tff(c_103, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_26, c_99])).
% 4.38/1.76  tff(c_196, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_189, c_103])).
% 4.38/1.76  tff(c_32, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.38/1.76  tff(c_207, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_196, c_32])).
% 4.38/1.76  tff(c_210, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_207])).
% 4.38/1.76  tff(c_223, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_210])).
% 4.38/1.76  tff(c_226, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_223])).
% 4.38/1.76  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_226])).
% 4.38/1.76  tff(c_231, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_210])).
% 4.38/1.76  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_203, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_60])).
% 4.38/1.76  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.38/1.76  tff(c_86, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_291, plain, (![B_438, A_439]: (v2_pre_topc(B_438) | ~m1_pre_topc(B_438, A_439) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.38/1.76  tff(c_297, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_291])).
% 4.38/1.76  tff(c_304, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_297])).
% 4.38/1.76  tff(c_42, plain, (![A_32]: (v3_pre_topc(k2_struct_0(A_32), A_32) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.38/1.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.38/1.76  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.38/1.76  tff(c_88, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_82, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_52, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_80, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_78, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_74, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_108, plain, (![A_420]: (u1_struct_0(A_420)=k2_struct_0(A_420) | ~l1_pre_topc(A_420))), inference(resolution, [status(thm)], [c_26, c_99])).
% 4.38/1.76  tff(c_116, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_78, c_108])).
% 4.38/1.76  tff(c_66, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_121, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_66])).
% 4.38/1.76  tff(c_202, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_121])).
% 4.38/1.76  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_150, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_64])).
% 4.38/1.76  tff(c_201, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_150])).
% 4.38/1.76  tff(c_185, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_74, c_176])).
% 4.38/1.76  tff(c_192, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_185])).
% 4.38/1.76  tff(c_44, plain, (![A_33]: (m1_pre_topc(A_33, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.38/1.76  tff(c_200, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_192, c_103])).
% 4.38/1.76  tff(c_62, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_212, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_200, c_62])).
% 4.38/1.76  tff(c_322, plain, (![A_445]: (m1_subset_1(u1_pre_topc(A_445), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_445)))) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.38/1.76  tff(c_334, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_200, c_322])).
% 4.38/1.76  tff(c_348, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_334])).
% 4.38/1.76  tff(c_24, plain, (![A_15, B_16]: (v1_pre_topc(g1_pre_topc(A_15, B_16)) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.38/1.76  tff(c_357, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_348, c_24])).
% 4.38/1.76  tff(c_365, plain, (v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_357])).
% 4.38/1.76  tff(c_382, plain, (![A_446]: (g1_pre_topc(u1_struct_0(A_446), u1_pre_topc(A_446))=A_446 | ~v1_pre_topc(A_446) | ~l1_pre_topc(A_446))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.38/1.76  tff(c_394, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_196, c_382])).
% 4.38/1.76  tff(c_406, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_365, c_394])).
% 4.38/1.76  tff(c_612, plain, (![C_453, A_454, D_455, B_456]: (C_453=A_454 | g1_pre_topc(C_453, D_455)!=g1_pre_topc(A_454, B_456) | ~m1_subset_1(B_456, k1_zfmisc_1(k1_zfmisc_1(A_454))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.38/1.76  tff(c_624, plain, (![C_453, D_455]: (k2_struct_0('#skF_3')=C_453 | g1_pre_topc(C_453, D_455)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_212, c_612])).
% 4.38/1.76  tff(c_629, plain, (![C_457, D_458]: (k2_struct_0('#skF_3')=C_457 | g1_pre_topc(C_457, D_458)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_348, c_624])).
% 4.38/1.76  tff(c_639, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_406, c_629])).
% 4.38/1.76  tff(c_645, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_639, c_212])).
% 4.38/1.76  tff(c_337, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_196, c_322])).
% 4.38/1.76  tff(c_350, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_337])).
% 4.38/1.76  tff(c_787, plain, (![D_469, B_470, C_471, A_472]: (D_469=B_470 | g1_pre_topc(C_471, D_469)!=g1_pre_topc(A_472, B_470) | ~m1_subset_1(B_470, k1_zfmisc_1(k1_zfmisc_1(A_472))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.38/1.76  tff(c_795, plain, (![D_469, C_471]: (u1_pre_topc('#skF_4')=D_469 | g1_pre_topc(C_471, D_469)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_406, c_787])).
% 4.38/1.76  tff(c_804, plain, (![D_473, C_474]: (u1_pre_topc('#skF_4')=D_473 | g1_pre_topc(C_474, D_473)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_795])).
% 4.38/1.76  tff(c_814, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_645, c_804])).
% 4.38/1.76  tff(c_648, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_639, c_200])).
% 4.38/1.76  tff(c_905, plain, (![A_481, B_482]: (m1_pre_topc(A_481, g1_pre_topc(u1_struct_0(B_482), u1_pre_topc(B_482))) | ~m1_pre_topc(A_481, B_482) | ~l1_pre_topc(B_482) | ~l1_pre_topc(A_481))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.38/1.76  tff(c_923, plain, (![A_481]: (m1_pre_topc(A_481, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_481, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_481))), inference(superposition, [status(thm), theory('equality')], [c_648, c_905])).
% 4.38/1.76  tff(c_958, plain, (![A_484]: (m1_pre_topc(A_484, '#skF_4') | ~m1_pre_topc(A_484, '#skF_3') | ~l1_pre_topc(A_484))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_406, c_814, c_923])).
% 4.38/1.76  tff(c_966, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_958])).
% 4.38/1.76  tff(c_972, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_966])).
% 4.38/1.76  tff(c_56, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_54, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.38/1.76  tff(c_90, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54])).
% 4.38/1.76  tff(c_1363, plain, (![F_520, C_524, D_521, H_519, E_522, A_518, B_523]: (r1_tmap_1(D_521, B_523, E_522, H_519) | ~r1_tmap_1(C_524, B_523, k3_tmap_1(A_518, B_523, D_521, C_524, E_522), H_519) | ~r1_tarski(F_520, u1_struct_0(C_524)) | ~r2_hidden(H_519, F_520) | ~v3_pre_topc(F_520, D_521) | ~m1_subset_1(H_519, u1_struct_0(C_524)) | ~m1_subset_1(H_519, u1_struct_0(D_521)) | ~m1_subset_1(F_520, k1_zfmisc_1(u1_struct_0(D_521))) | ~m1_pre_topc(C_524, D_521) | ~m1_subset_1(E_522, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_521), u1_struct_0(B_523)))) | ~v1_funct_2(E_522, u1_struct_0(D_521), u1_struct_0(B_523)) | ~v1_funct_1(E_522) | ~m1_pre_topc(D_521, A_518) | v2_struct_0(D_521) | ~m1_pre_topc(C_524, A_518) | v2_struct_0(C_524) | ~l1_pre_topc(B_523) | ~v2_pre_topc(B_523) | v2_struct_0(B_523) | ~l1_pre_topc(A_518) | ~v2_pre_topc(A_518) | v2_struct_0(A_518))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.38/1.76  tff(c_1365, plain, (![F_520]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_520, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_520) | ~v3_pre_topc(F_520, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_520, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_90, c_1363])).
% 4.38/1.76  tff(c_1368, plain, (![F_520]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_520, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', F_520) | ~v3_pre_topc(F_520, '#skF_4') | ~m1_subset_1(F_520, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_74, c_70, c_68, c_202, c_116, c_196, c_201, c_116, c_196, c_972, c_196, c_203, c_196, c_203, c_648, c_648, c_1365])).
% 4.38/1.76  tff(c_1376, plain, (![F_527]: (~r1_tarski(F_527, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', F_527) | ~v3_pre_topc(F_527, '#skF_4') | ~m1_subset_1(F_527, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_76, c_72, c_52, c_1368])).
% 4.38/1.76  tff(c_1386, plain, (![A_528]: (~r2_hidden('#skF_6', A_528) | ~v3_pre_topc(A_528, '#skF_4') | ~r1_tarski(A_528, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_1376])).
% 4.38/1.76  tff(c_1391, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6, c_1386])).
% 4.38/1.76  tff(c_1392, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1391])).
% 4.38/1.76  tff(c_1395, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1392])).
% 4.38/1.76  tff(c_1399, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_304, c_189, c_1395])).
% 4.38/1.76  tff(c_1400, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1391])).
% 4.38/1.76  tff(c_1404, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_1400])).
% 4.38/1.76  tff(c_1407, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1404])).
% 4.38/1.76  tff(c_1409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_231, c_1407])).
% 4.38/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.38/1.76  
% 4.38/1.76  Inference rules
% 4.38/1.76  ----------------------
% 4.38/1.76  #Ref     : 2
% 4.38/1.76  #Sup     : 278
% 4.38/1.76  #Fact    : 0
% 4.38/1.76  #Define  : 0
% 4.38/1.76  #Split   : 12
% 4.38/1.76  #Chain   : 0
% 4.38/1.76  #Close   : 0
% 4.38/1.76  
% 4.38/1.76  Ordering : KBO
% 4.38/1.76  
% 4.38/1.76  Simplification rules
% 4.38/1.76  ----------------------
% 4.38/1.76  #Subsume      : 27
% 4.38/1.76  #Demod        : 288
% 4.38/1.76  #Tautology    : 111
% 4.38/1.76  #SimpNegUnit  : 11
% 4.38/1.76  #BackRed      : 17
% 4.38/1.76  
% 4.38/1.76  #Partial instantiations: 0
% 4.38/1.76  #Strategies tried      : 1
% 4.38/1.76  
% 4.38/1.76  Timing (in seconds)
% 4.38/1.76  ----------------------
% 4.38/1.76  Preprocessing        : 0.42
% 4.38/1.76  Parsing              : 0.22
% 4.38/1.76  CNF conversion       : 0.05
% 4.38/1.76  Main loop            : 0.50
% 4.38/1.76  Inferencing          : 0.16
% 4.38/1.76  Reduction            : 0.18
% 4.38/1.76  Demodulation         : 0.13
% 4.38/1.76  BG Simplification    : 0.03
% 4.38/1.76  Subsumption          : 0.09
% 4.38/1.76  Abstraction          : 0.02
% 4.38/1.76  MUC search           : 0.00
% 4.38/1.76  Cooper               : 0.00
% 4.38/1.76  Total                : 0.96
% 4.38/1.76  Index Insertion      : 0.00
% 4.38/1.76  Index Deletion       : 0.00
% 4.38/1.76  Index Matching       : 0.00
% 4.38/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
