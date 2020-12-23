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
% DateTime   : Thu Dec  3 10:27:28 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.99s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 355 expanded)
%              Number of leaves         :   43 ( 152 expanded)
%              Depth                    :   14
%              Number of atoms          :  416 (2594 expanded)
%              Number of equality atoms :    6 ( 112 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_302,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_127,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_251,axiom,(
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

tff(f_194,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_40,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_85,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_119,plain,(
    ! [B_557,A_558] :
      ( v2_pre_topc(B_557)
      | ~ m1_pre_topc(B_557,A_558)
      | ~ l1_pre_topc(A_558)
      | ~ v2_pre_topc(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_119])).

tff(c_134,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_125])).

tff(c_92,plain,(
    ! [B_551,A_552] :
      ( l1_pre_topc(B_551)
      | ~ m1_pre_topc(B_551,A_552)
      | ~ l1_pre_topc(A_552) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_92])).

tff(c_107,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_98])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_150,plain,(
    ! [B_565,A_566] :
      ( m1_subset_1(u1_struct_0(B_565),k1_zfmisc_1(u1_struct_0(A_566)))
      | ~ m1_pre_topc(B_565,A_566)
      | ~ l1_pre_topc(A_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_195,plain,(
    ! [A_577,A_578,B_579] :
      ( m1_subset_1(A_577,u1_struct_0(A_578))
      | ~ r2_hidden(A_577,u1_struct_0(B_579))
      | ~ m1_pre_topc(B_579,A_578)
      | ~ l1_pre_topc(A_578) ) ),
    inference(resolution,[status(thm)],[c_150,c_10])).

tff(c_203,plain,(
    ! [A_582,A_583,B_584] :
      ( m1_subset_1(A_582,u1_struct_0(A_583))
      | ~ m1_pre_topc(B_584,A_583)
      | ~ l1_pre_topc(A_583)
      | v1_xboole_0(u1_struct_0(B_584))
      | ~ m1_subset_1(A_582,u1_struct_0(B_584)) ) ),
    inference(resolution,[status(thm)],[c_8,c_195])).

tff(c_209,plain,(
    ! [A_582] :
      ( m1_subset_1(A_582,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_582,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_60,c_203])).

tff(c_218,plain,(
    ! [A_582] :
      ( m1_subset_1(A_582,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_582,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_209])).

tff(c_379,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( m1_connsp_2('#skF_1'(A_21,B_22),A_21,B_22)
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_375,plain,(
    ! [C_630,A_631,B_632] :
      ( m1_subset_1(C_630,k1_zfmisc_1(u1_struct_0(A_631)))
      | ~ m1_connsp_2(C_630,A_631,B_632)
      | ~ m1_subset_1(B_632,u1_struct_0(A_631))
      | ~ l1_pre_topc(A_631)
      | ~ v2_pre_topc(A_631)
      | v2_struct_0(A_631) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_378,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1('#skF_1'(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_375])).

tff(c_538,plain,(
    ! [C_666,B_667,A_668] :
      ( r2_hidden(C_666,B_667)
      | ~ m1_connsp_2(B_667,A_668,C_666)
      | ~ m1_subset_1(C_666,u1_struct_0(A_668))
      | ~ m1_subset_1(B_667,k1_zfmisc_1(u1_struct_0(A_668)))
      | ~ l1_pre_topc(A_668)
      | ~ v2_pre_topc(A_668)
      | v2_struct_0(A_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_542,plain,(
    ! [B_669,A_670] :
      ( r2_hidden(B_669,'#skF_1'(A_670,B_669))
      | ~ m1_subset_1('#skF_1'(A_670,B_669),k1_zfmisc_1(u1_struct_0(A_670)))
      | ~ m1_subset_1(B_669,u1_struct_0(A_670))
      | ~ l1_pre_topc(A_670)
      | ~ v2_pre_topc(A_670)
      | v2_struct_0(A_670) ) ),
    inference(resolution,[status(thm)],[c_20,c_538])).

tff(c_546,plain,(
    ! [B_671,A_672] :
      ( r2_hidden(B_671,'#skF_1'(A_672,B_671))
      | ~ m1_subset_1(B_671,u1_struct_0(A_672))
      | ~ l1_pre_topc(A_672)
      | ~ v2_pre_topc(A_672)
      | v2_struct_0(A_672) ) ),
    inference(resolution,[status(thm)],[c_378,c_542])).

tff(c_420,plain,(
    ! [A_641,B_642] :
      ( m1_subset_1('#skF_1'(A_641,B_642),k1_zfmisc_1(u1_struct_0(A_641)))
      | ~ m1_subset_1(B_642,u1_struct_0(A_641))
      | ~ l1_pre_topc(A_641)
      | ~ v2_pre_topc(A_641)
      | v2_struct_0(A_641) ) ),
    inference(resolution,[status(thm)],[c_20,c_375])).

tff(c_12,plain,(
    ! [C_10,B_9,A_8] :
      ( ~ v1_xboole_0(C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_426,plain,(
    ! [A_641,A_8,B_642] :
      ( ~ v1_xboole_0(u1_struct_0(A_641))
      | ~ r2_hidden(A_8,'#skF_1'(A_641,B_642))
      | ~ m1_subset_1(B_642,u1_struct_0(A_641))
      | ~ l1_pre_topc(A_641)
      | ~ v2_pre_topc(A_641)
      | v2_struct_0(A_641) ) ),
    inference(resolution,[status(thm)],[c_420,c_12])).

tff(c_555,plain,(
    ! [A_673,B_674] :
      ( ~ v1_xboole_0(u1_struct_0(A_673))
      | ~ m1_subset_1(B_674,u1_struct_0(A_673))
      | ~ l1_pre_topc(A_673)
      | ~ v2_pre_topc(A_673)
      | v2_struct_0(A_673) ) ),
    inference(resolution,[status(thm)],[c_546,c_426])).

tff(c_567,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_555])).

tff(c_579,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_107,c_379,c_567])).

tff(c_581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_579])).

tff(c_583,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_95,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_95])).

tff(c_122,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_131,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_122])).

tff(c_48,plain,(
    v1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_30,plain,(
    ! [B_40,A_38] :
      ( m1_subset_1(u1_struct_0(B_40),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_584,plain,(
    ! [B_675,A_676] :
      ( v3_pre_topc(u1_struct_0(B_675),A_676)
      | ~ v1_tsep_1(B_675,A_676)
      | ~ m1_subset_1(u1_struct_0(B_675),k1_zfmisc_1(u1_struct_0(A_676)))
      | ~ m1_pre_topc(B_675,A_676)
      | ~ l1_pre_topc(A_676)
      | ~ v2_pre_topc(A_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_588,plain,(
    ! [B_40,A_38] :
      ( v3_pre_topc(u1_struct_0(B_40),A_38)
      | ~ v1_tsep_1(B_40,A_38)
      | ~ v2_pre_topc(A_38)
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_30,c_584])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_82,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_83,plain,
    ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_140,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_76,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_84,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_76])).

tff(c_201,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_84])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_302])).

tff(c_782,plain,(
    ! [B_728,F_727,C_722,A_724,D_726,H_723,E_725] :
      ( r1_tmap_1(D_726,B_728,E_725,H_723)
      | ~ r1_tmap_1(C_722,B_728,k3_tmap_1(A_724,B_728,D_726,C_722,E_725),H_723)
      | ~ r1_tarski(F_727,u1_struct_0(C_722))
      | ~ r2_hidden(H_723,F_727)
      | ~ v3_pre_topc(F_727,D_726)
      | ~ m1_subset_1(H_723,u1_struct_0(C_722))
      | ~ m1_subset_1(H_723,u1_struct_0(D_726))
      | ~ m1_subset_1(F_727,k1_zfmisc_1(u1_struct_0(D_726)))
      | ~ m1_pre_topc(C_722,D_726)
      | ~ m1_subset_1(E_725,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_726),u1_struct_0(B_728))))
      | ~ v1_funct_2(E_725,u1_struct_0(D_726),u1_struct_0(B_728))
      | ~ v1_funct_1(E_725)
      | ~ m1_pre_topc(D_726,A_724)
      | v2_struct_0(D_726)
      | ~ m1_pre_topc(C_722,A_724)
      | v2_struct_0(C_722)
      | ~ l1_pre_topc(B_728)
      | ~ v2_pre_topc(B_728)
      | v2_struct_0(B_728)
      | ~ l1_pre_topc(A_724)
      | ~ v2_pre_topc(A_724)
      | v2_struct_0(A_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_786,plain,(
    ! [F_727] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ r1_tarski(F_727,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_727)
      | ~ v3_pre_topc(F_727,'#skF_5')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_727,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_140,c_782])).

tff(c_793,plain,(
    ! [F_727] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ r1_tarski(F_727,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_727)
      | ~ v3_pre_topc(F_727,'#skF_5')
      | ~ m1_subset_1(F_727,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_52,c_50,c_46,c_85,c_42,c_786])).

tff(c_796,plain,(
    ! [F_729] :
      ( ~ r1_tarski(F_729,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',F_729)
      | ~ v3_pre_topc(F_729,'#skF_5')
      | ~ m1_subset_1(F_729,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_201,c_793])).

tff(c_804,plain,(
    ! [B_40] :
      ( ~ r1_tarski(u1_struct_0(B_40),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_40))
      | ~ v3_pre_topc(u1_struct_0(B_40),'#skF_5')
      | ~ m1_pre_topc(B_40,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_796])).

tff(c_813,plain,(
    ! [B_732] :
      ( ~ r1_tarski(u1_struct_0(B_732),u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_8',u1_struct_0(B_732))
      | ~ v3_pre_topc(u1_struct_0(B_732),'#skF_5')
      | ~ m1_pre_topc(B_732,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_804])).

tff(c_817,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_813])).

tff(c_820,plain,
    ( ~ r2_hidden('#skF_8',u1_struct_0('#skF_4'))
    | ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_817])).

tff(c_821,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_820])).

tff(c_824,plain,
    ( ~ v1_tsep_1('#skF_4','#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_588,c_821])).

tff(c_828,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_46,c_131,c_48,c_824])).

tff(c_829,plain,(
    ~ r2_hidden('#skF_8',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_820])).

tff(c_839,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_829])).

tff(c_842,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_839])).

tff(c_844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_842])).

tff(c_845,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_1401,plain,(
    ! [D_880,E_877,G_881,A_878,B_882,C_879] :
      ( r1_tmap_1(D_880,B_882,k3_tmap_1(A_878,B_882,C_879,D_880,E_877),G_881)
      | ~ r1_tmap_1(C_879,B_882,E_877,G_881)
      | ~ m1_pre_topc(D_880,C_879)
      | ~ m1_subset_1(G_881,u1_struct_0(D_880))
      | ~ m1_subset_1(G_881,u1_struct_0(C_879))
      | ~ m1_subset_1(E_877,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_879),u1_struct_0(B_882))))
      | ~ v1_funct_2(E_877,u1_struct_0(C_879),u1_struct_0(B_882))
      | ~ v1_funct_1(E_877)
      | ~ m1_pre_topc(D_880,A_878)
      | v2_struct_0(D_880)
      | ~ m1_pre_topc(C_879,A_878)
      | v2_struct_0(C_879)
      | ~ l1_pre_topc(B_882)
      | ~ v2_pre_topc(B_882)
      | v2_struct_0(B_882)
      | ~ l1_pre_topc(A_878)
      | ~ v2_pre_topc(A_878)
      | v2_struct_0(A_878) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1403,plain,(
    ! [D_880,A_878,G_881] :
      ( r1_tmap_1(D_880,'#skF_3',k3_tmap_1(A_878,'#skF_3','#skF_5',D_880,'#skF_6'),G_881)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_881)
      | ~ m1_pre_topc(D_880,'#skF_5')
      | ~ m1_subset_1(G_881,u1_struct_0(D_880))
      | ~ m1_subset_1(G_881,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_880,A_878)
      | v2_struct_0(D_880)
      | ~ m1_pre_topc('#skF_5',A_878)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_878)
      | ~ v2_pre_topc(A_878)
      | v2_struct_0(A_878) ) ),
    inference(resolution,[status(thm)],[c_50,c_1401])).

tff(c_1406,plain,(
    ! [D_880,A_878,G_881] :
      ( r1_tmap_1(D_880,'#skF_3',k3_tmap_1(A_878,'#skF_3','#skF_5',D_880,'#skF_6'),G_881)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_881)
      | ~ m1_pre_topc(D_880,'#skF_5')
      | ~ m1_subset_1(G_881,u1_struct_0(D_880))
      | ~ m1_subset_1(G_881,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_880,A_878)
      | v2_struct_0(D_880)
      | ~ m1_pre_topc('#skF_5',A_878)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_878)
      | ~ v2_pre_topc(A_878)
      | v2_struct_0(A_878) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_52,c_1403])).

tff(c_1409,plain,(
    ! [D_884,A_885,G_886] :
      ( r1_tmap_1(D_884,'#skF_3',k3_tmap_1(A_885,'#skF_3','#skF_5',D_884,'#skF_6'),G_886)
      | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6',G_886)
      | ~ m1_pre_topc(D_884,'#skF_5')
      | ~ m1_subset_1(G_886,u1_struct_0(D_884))
      | ~ m1_subset_1(G_886,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_884,A_885)
      | v2_struct_0(D_884)
      | ~ m1_pre_topc('#skF_5',A_885)
      | ~ l1_pre_topc(A_885)
      | ~ v2_pre_topc(A_885)
      | v2_struct_0(A_885) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_1406])).

tff(c_853,plain,(
    ~ r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_84])).

tff(c_1412,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1409,c_853])).

tff(c_1415,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_56,c_60,c_85,c_42,c_46,c_845,c_1412])).

tff(c_1417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_62,c_1415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:58:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.82  
% 4.68/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.82  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.68/1.82  
% 4.68/1.82  %Foreground sorts:
% 4.68/1.82  
% 4.68/1.82  
% 4.68/1.82  %Background operators:
% 4.68/1.82  
% 4.68/1.82  
% 4.68/1.82  %Foreground operators:
% 4.68/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.68/1.82  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.68/1.82  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.68/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.68/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.82  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.68/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.68/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.68/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.68/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.82  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.68/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.68/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.68/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.68/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.68/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.82  
% 4.99/1.85  tff(f_302, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.99/1.85  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.99/1.85  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.99/1.85  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.99/1.85  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.99/1.85  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.99/1.85  tff(f_92, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.99/1.85  tff(f_80, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.99/1.85  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 4.99/1.85  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.99/1.85  tff(f_127, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.99/1.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.99/1.85  tff(f_251, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.99/1.85  tff(f_194, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.99/1.85  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_40, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_85, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 4.99/1.85  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_119, plain, (![B_557, A_558]: (v2_pre_topc(B_557) | ~m1_pre_topc(B_557, A_558) | ~l1_pre_topc(A_558) | ~v2_pre_topc(A_558))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.99/1.85  tff(c_125, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_119])).
% 4.99/1.85  tff(c_134, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_125])).
% 4.99/1.85  tff(c_92, plain, (![B_551, A_552]: (l1_pre_topc(B_551) | ~m1_pre_topc(B_551, A_552) | ~l1_pre_topc(A_552))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.99/1.85  tff(c_98, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_92])).
% 4.99/1.85  tff(c_107, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_98])).
% 4.99/1.85  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.99/1.85  tff(c_150, plain, (![B_565, A_566]: (m1_subset_1(u1_struct_0(B_565), k1_zfmisc_1(u1_struct_0(A_566))) | ~m1_pre_topc(B_565, A_566) | ~l1_pre_topc(A_566))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.99/1.85  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.99/1.85  tff(c_195, plain, (![A_577, A_578, B_579]: (m1_subset_1(A_577, u1_struct_0(A_578)) | ~r2_hidden(A_577, u1_struct_0(B_579)) | ~m1_pre_topc(B_579, A_578) | ~l1_pre_topc(A_578))), inference(resolution, [status(thm)], [c_150, c_10])).
% 4.99/1.85  tff(c_203, plain, (![A_582, A_583, B_584]: (m1_subset_1(A_582, u1_struct_0(A_583)) | ~m1_pre_topc(B_584, A_583) | ~l1_pre_topc(A_583) | v1_xboole_0(u1_struct_0(B_584)) | ~m1_subset_1(A_582, u1_struct_0(B_584)))), inference(resolution, [status(thm)], [c_8, c_195])).
% 4.99/1.85  tff(c_209, plain, (![A_582]: (m1_subset_1(A_582, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_582, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_60, c_203])).
% 4.99/1.85  tff(c_218, plain, (![A_582]: (m1_subset_1(A_582, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_582, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_209])).
% 4.99/1.85  tff(c_379, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_218])).
% 4.99/1.85  tff(c_20, plain, (![A_21, B_22]: (m1_connsp_2('#skF_1'(A_21, B_22), A_21, B_22) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.99/1.85  tff(c_375, plain, (![C_630, A_631, B_632]: (m1_subset_1(C_630, k1_zfmisc_1(u1_struct_0(A_631))) | ~m1_connsp_2(C_630, A_631, B_632) | ~m1_subset_1(B_632, u1_struct_0(A_631)) | ~l1_pre_topc(A_631) | ~v2_pre_topc(A_631) | v2_struct_0(A_631))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.99/1.85  tff(c_378, plain, (![A_21, B_22]: (m1_subset_1('#skF_1'(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(resolution, [status(thm)], [c_20, c_375])).
% 4.99/1.85  tff(c_538, plain, (![C_666, B_667, A_668]: (r2_hidden(C_666, B_667) | ~m1_connsp_2(B_667, A_668, C_666) | ~m1_subset_1(C_666, u1_struct_0(A_668)) | ~m1_subset_1(B_667, k1_zfmisc_1(u1_struct_0(A_668))) | ~l1_pre_topc(A_668) | ~v2_pre_topc(A_668) | v2_struct_0(A_668))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.99/1.85  tff(c_542, plain, (![B_669, A_670]: (r2_hidden(B_669, '#skF_1'(A_670, B_669)) | ~m1_subset_1('#skF_1'(A_670, B_669), k1_zfmisc_1(u1_struct_0(A_670))) | ~m1_subset_1(B_669, u1_struct_0(A_670)) | ~l1_pre_topc(A_670) | ~v2_pre_topc(A_670) | v2_struct_0(A_670))), inference(resolution, [status(thm)], [c_20, c_538])).
% 4.99/1.85  tff(c_546, plain, (![B_671, A_672]: (r2_hidden(B_671, '#skF_1'(A_672, B_671)) | ~m1_subset_1(B_671, u1_struct_0(A_672)) | ~l1_pre_topc(A_672) | ~v2_pre_topc(A_672) | v2_struct_0(A_672))), inference(resolution, [status(thm)], [c_378, c_542])).
% 4.99/1.85  tff(c_420, plain, (![A_641, B_642]: (m1_subset_1('#skF_1'(A_641, B_642), k1_zfmisc_1(u1_struct_0(A_641))) | ~m1_subset_1(B_642, u1_struct_0(A_641)) | ~l1_pre_topc(A_641) | ~v2_pre_topc(A_641) | v2_struct_0(A_641))), inference(resolution, [status(thm)], [c_20, c_375])).
% 4.99/1.85  tff(c_12, plain, (![C_10, B_9, A_8]: (~v1_xboole_0(C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.99/1.85  tff(c_426, plain, (![A_641, A_8, B_642]: (~v1_xboole_0(u1_struct_0(A_641)) | ~r2_hidden(A_8, '#skF_1'(A_641, B_642)) | ~m1_subset_1(B_642, u1_struct_0(A_641)) | ~l1_pre_topc(A_641) | ~v2_pre_topc(A_641) | v2_struct_0(A_641))), inference(resolution, [status(thm)], [c_420, c_12])).
% 4.99/1.85  tff(c_555, plain, (![A_673, B_674]: (~v1_xboole_0(u1_struct_0(A_673)) | ~m1_subset_1(B_674, u1_struct_0(A_673)) | ~l1_pre_topc(A_673) | ~v2_pre_topc(A_673) | v2_struct_0(A_673))), inference(resolution, [status(thm)], [c_546, c_426])).
% 4.99/1.85  tff(c_567, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_555])).
% 4.99/1.85  tff(c_579, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_107, c_379, c_567])).
% 4.99/1.85  tff(c_581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_579])).
% 4.99/1.85  tff(c_583, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_218])).
% 4.99/1.85  tff(c_95, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_92])).
% 4.99/1.85  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_95])).
% 4.99/1.85  tff(c_122, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_119])).
% 4.99/1.85  tff(c_131, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_122])).
% 4.99/1.85  tff(c_48, plain, (v1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_30, plain, (![B_40, A_38]: (m1_subset_1(u1_struct_0(B_40), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_pre_topc(B_40, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.99/1.85  tff(c_584, plain, (![B_675, A_676]: (v3_pre_topc(u1_struct_0(B_675), A_676) | ~v1_tsep_1(B_675, A_676) | ~m1_subset_1(u1_struct_0(B_675), k1_zfmisc_1(u1_struct_0(A_676))) | ~m1_pre_topc(B_675, A_676) | ~l1_pre_topc(A_676) | ~v2_pre_topc(A_676))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.99/1.85  tff(c_588, plain, (![B_40, A_38]: (v3_pre_topc(u1_struct_0(B_40), A_38) | ~v1_tsep_1(B_40, A_38) | ~v2_pre_topc(A_38) | ~m1_pre_topc(B_40, A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_30, c_584])).
% 4.99/1.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.99/1.85  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_82, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_83, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 4.99/1.85  tff(c_140, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_83])).
% 4.99/1.85  tff(c_76, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_84, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_76])).
% 4.99/1.85  tff(c_201, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_84])).
% 4.99/1.85  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_302])).
% 4.99/1.85  tff(c_782, plain, (![B_728, F_727, C_722, A_724, D_726, H_723, E_725]: (r1_tmap_1(D_726, B_728, E_725, H_723) | ~r1_tmap_1(C_722, B_728, k3_tmap_1(A_724, B_728, D_726, C_722, E_725), H_723) | ~r1_tarski(F_727, u1_struct_0(C_722)) | ~r2_hidden(H_723, F_727) | ~v3_pre_topc(F_727, D_726) | ~m1_subset_1(H_723, u1_struct_0(C_722)) | ~m1_subset_1(H_723, u1_struct_0(D_726)) | ~m1_subset_1(F_727, k1_zfmisc_1(u1_struct_0(D_726))) | ~m1_pre_topc(C_722, D_726) | ~m1_subset_1(E_725, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_726), u1_struct_0(B_728)))) | ~v1_funct_2(E_725, u1_struct_0(D_726), u1_struct_0(B_728)) | ~v1_funct_1(E_725) | ~m1_pre_topc(D_726, A_724) | v2_struct_0(D_726) | ~m1_pre_topc(C_722, A_724) | v2_struct_0(C_722) | ~l1_pre_topc(B_728) | ~v2_pre_topc(B_728) | v2_struct_0(B_728) | ~l1_pre_topc(A_724) | ~v2_pre_topc(A_724) | v2_struct_0(A_724))), inference(cnfTransformation, [status(thm)], [f_251])).
% 4.99/1.85  tff(c_786, plain, (![F_727]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~r1_tarski(F_727, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_727) | ~v3_pre_topc(F_727, '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_727, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_140, c_782])).
% 4.99/1.85  tff(c_793, plain, (![F_727]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~r1_tarski(F_727, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_727) | ~v3_pre_topc(F_727, '#skF_5') | ~m1_subset_1(F_727, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_52, c_50, c_46, c_85, c_42, c_786])).
% 4.99/1.85  tff(c_796, plain, (![F_729]: (~r1_tarski(F_729, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', F_729) | ~v3_pre_topc(F_729, '#skF_5') | ~m1_subset_1(F_729, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_201, c_793])).
% 4.99/1.85  tff(c_804, plain, (![B_40]: (~r1_tarski(u1_struct_0(B_40), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', u1_struct_0(B_40)) | ~v3_pre_topc(u1_struct_0(B_40), '#skF_5') | ~m1_pre_topc(B_40, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_796])).
% 4.99/1.85  tff(c_813, plain, (![B_732]: (~r1_tarski(u1_struct_0(B_732), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_8', u1_struct_0(B_732)) | ~v3_pre_topc(u1_struct_0(B_732), '#skF_5') | ~m1_pre_topc(B_732, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_804])).
% 4.99/1.85  tff(c_817, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_813])).
% 4.99/1.85  tff(c_820, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_4')) | ~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_817])).
% 4.99/1.85  tff(c_821, plain, (~v3_pre_topc(u1_struct_0('#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_820])).
% 4.99/1.85  tff(c_824, plain, (~v1_tsep_1('#skF_4', '#skF_5') | ~v2_pre_topc('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_588, c_821])).
% 4.99/1.85  tff(c_828, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_46, c_131, c_48, c_824])).
% 4.99/1.85  tff(c_829, plain, (~r2_hidden('#skF_8', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_820])).
% 4.99/1.85  tff(c_839, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_829])).
% 4.99/1.85  tff(c_842, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_839])).
% 4.99/1.85  tff(c_844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_583, c_842])).
% 4.99/1.85  tff(c_845, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_83])).
% 4.99/1.85  tff(c_1401, plain, (![D_880, E_877, G_881, A_878, B_882, C_879]: (r1_tmap_1(D_880, B_882, k3_tmap_1(A_878, B_882, C_879, D_880, E_877), G_881) | ~r1_tmap_1(C_879, B_882, E_877, G_881) | ~m1_pre_topc(D_880, C_879) | ~m1_subset_1(G_881, u1_struct_0(D_880)) | ~m1_subset_1(G_881, u1_struct_0(C_879)) | ~m1_subset_1(E_877, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_879), u1_struct_0(B_882)))) | ~v1_funct_2(E_877, u1_struct_0(C_879), u1_struct_0(B_882)) | ~v1_funct_1(E_877) | ~m1_pre_topc(D_880, A_878) | v2_struct_0(D_880) | ~m1_pre_topc(C_879, A_878) | v2_struct_0(C_879) | ~l1_pre_topc(B_882) | ~v2_pre_topc(B_882) | v2_struct_0(B_882) | ~l1_pre_topc(A_878) | ~v2_pre_topc(A_878) | v2_struct_0(A_878))), inference(cnfTransformation, [status(thm)], [f_194])).
% 4.99/1.85  tff(c_1403, plain, (![D_880, A_878, G_881]: (r1_tmap_1(D_880, '#skF_3', k3_tmap_1(A_878, '#skF_3', '#skF_5', D_880, '#skF_6'), G_881) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_881) | ~m1_pre_topc(D_880, '#skF_5') | ~m1_subset_1(G_881, u1_struct_0(D_880)) | ~m1_subset_1(G_881, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_880, A_878) | v2_struct_0(D_880) | ~m1_pre_topc('#skF_5', A_878) | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_878) | ~v2_pre_topc(A_878) | v2_struct_0(A_878))), inference(resolution, [status(thm)], [c_50, c_1401])).
% 4.99/1.85  tff(c_1406, plain, (![D_880, A_878, G_881]: (r1_tmap_1(D_880, '#skF_3', k3_tmap_1(A_878, '#skF_3', '#skF_5', D_880, '#skF_6'), G_881) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_881) | ~m1_pre_topc(D_880, '#skF_5') | ~m1_subset_1(G_881, u1_struct_0(D_880)) | ~m1_subset_1(G_881, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_880, A_878) | v2_struct_0(D_880) | ~m1_pre_topc('#skF_5', A_878) | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_878) | ~v2_pre_topc(A_878) | v2_struct_0(A_878))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_52, c_1403])).
% 4.99/1.85  tff(c_1409, plain, (![D_884, A_885, G_886]: (r1_tmap_1(D_884, '#skF_3', k3_tmap_1(A_885, '#skF_3', '#skF_5', D_884, '#skF_6'), G_886) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', G_886) | ~m1_pre_topc(D_884, '#skF_5') | ~m1_subset_1(G_886, u1_struct_0(D_884)) | ~m1_subset_1(G_886, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_884, A_885) | v2_struct_0(D_884) | ~m1_pre_topc('#skF_5', A_885) | ~l1_pre_topc(A_885) | ~v2_pre_topc(A_885) | v2_struct_0(A_885))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_1406])).
% 4.99/1.85  tff(c_853, plain, (~r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_84])).
% 4.99/1.85  tff(c_1412, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1409, c_853])).
% 4.99/1.85  tff(c_1415, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_56, c_60, c_85, c_42, c_46, c_845, c_1412])).
% 4.99/1.85  tff(c_1417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_62, c_1415])).
% 4.99/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.99/1.85  
% 4.99/1.85  Inference rules
% 4.99/1.85  ----------------------
% 4.99/1.85  #Ref     : 0
% 4.99/1.85  #Sup     : 240
% 4.99/1.85  #Fact    : 0
% 4.99/1.85  #Define  : 0
% 4.99/1.85  #Split   : 18
% 4.99/1.85  #Chain   : 0
% 4.99/1.85  #Close   : 0
% 4.99/1.85  
% 4.99/1.85  Ordering : KBO
% 4.99/1.85  
% 4.99/1.85  Simplification rules
% 4.99/1.85  ----------------------
% 4.99/1.85  #Subsume      : 75
% 4.99/1.85  #Demod        : 282
% 4.99/1.85  #Tautology    : 56
% 4.99/1.85  #SimpNegUnit  : 44
% 4.99/1.85  #BackRed      : 0
% 4.99/1.85  
% 4.99/1.85  #Partial instantiations: 0
% 4.99/1.85  #Strategies tried      : 1
% 4.99/1.85  
% 4.99/1.85  Timing (in seconds)
% 4.99/1.85  ----------------------
% 4.99/1.85  Preprocessing        : 0.42
% 4.99/1.85  Parsing              : 0.21
% 4.99/1.85  CNF conversion       : 0.07
% 4.99/1.85  Main loop            : 0.58
% 4.99/1.85  Inferencing          : 0.22
% 4.99/1.85  Reduction            : 0.17
% 4.99/1.85  Demodulation         : 0.12
% 4.99/1.85  BG Simplification    : 0.03
% 4.99/1.85  Subsumption          : 0.11
% 4.99/1.85  Abstraction          : 0.02
% 4.99/1.85  MUC search           : 0.00
% 4.99/1.85  Cooper               : 0.00
% 4.99/1.85  Total                : 1.05
% 4.99/1.85  Index Insertion      : 0.00
% 4.99/1.85  Index Deletion       : 0.00
% 4.99/1.85  Index Matching       : 0.00
% 4.99/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
